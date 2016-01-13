{-# LANGUAGE PatternSynonyms, NoMonomorphismRestriction, OverloadedStrings, LambdaCase, RoleAnnotations #-} 
{-# OPTIONS -fno-warn-unticked-promoted-constructors #-} 

module Database.Design.Ampersand.ECA2SQL 
  ( module Database.Design.Ampersand.ECA2SQL
  ) where 

import Database.Design.Ampersand.Core.AbstractSyntaxTree 
  ( ECArule(..), PAclause(..), Expression(..), Declaration(..), AAtomValue(..), InsDel(..), Event(..)
  , A_Context(..), ObjectDef(..), ObjectDef(..), Origin(..), Cruds(..)
  )
import Database.Design.Ampersand.FSpec (FSpec(..), SqlTType(..)) 
import Language.SQL.SimpleSQL.Syntax 
  ( QueryExpr(..), ValueExpr(..), Name(..), TableRef(..), InPredValue(..), SubQueryExprType(..) 
  , makeSelect
  ) 
import Database.Design.Ampersand.FSpec.FSpec (PlugSQL(..), PlugInfo(..))
import Database.Design.Ampersand.FSpec.ToFSpec.ADL2Plug 
import Database.Design.Ampersand.FSpec.SQL (expr2SQL) 
import Database.Design.Ampersand.FSpec.FSpecAux (getDeclarationTableInfo,getConceptTableInfo)
import Database.Design.Ampersand.Basics (Named(..))
import Database.Design.Ampersand.Core.ParseTree (makePSingleton)
import Database.Design.Ampersand.ECA2SQL.Utils  () 

-- A specification of a table contains the name of that table and all of its columns.
data TableSpec = TableSpec 
  { tableName :: Name 
  , tableColumns :: [Name] 
  } 

-- A type representing table expressions composed of ampersand values. 
data TableValue = TableValue { columnAliases :: [ Maybe Name ], tableRows :: [ [AAtomValue] ] } 

data RowValue a = RowValue { getRowValue :: [ (Maybe Name, a) ] } 

-- A type represeting a vector of values. 
newtype VectorValue a = VectorValue { getVectorValue :: [a] }

-- Used to distinguish sql methods from statements. The only difference 
-- is that a method cannot be "sequenced" with `:>>='. Essentially this
-- allows us to define 
data SQLSem = Stmt | Mthd 

type SQLStatement = SQLSt 'Stmt

-- TODO: Mock database which runs SQL statements
data SQLMethod a = SQLMethod 
  { mtdName :: Name 
  , mtdParams :: [Name] 
  , mtdBody :: SQLSt 'Mthd a 
  }

type role SQLMethod nominal 
newtype SQLMethodName a = MthdName { getMthdName :: Name }

-- Types which can be interpretted in the domain of sql expressions 
data SQLType a where 
  -- Expression types 
  SQLRef    :: SQLType Name
  SQLMthd   :: SQLType a -> SQLType (SQLMethodName a) 
  SQLGRef   :: SQLType ValueExpr

  -- Values types
  SQLScalar :: SQLType AAtomValue 
  SQLTable  :: SQLType TableValue
  SQLUnit   :: SQLType () 
  SQLVec    :: SQLType a -> SQLType (VectorValue a)
  SQLRow    :: SQLType a -> SQLType (RowValue a) 

class IsSQLType a where sqlType :: SQLType a 
instance IsSQLType Name where sqlType = SQLRef
instance IsSQLType ValueExpr where sqlType = SQLGRef  

instance IsSQLType AAtomValue where sqlType = SQLScalar  
instance IsSQLType TableValue where sqlType = SQLTable
instance IsSQLType () where sqlType = SQLUnit    
instance IsSQLType a => IsSQLType (VectorValue a) where sqlType = SQLVec sqlType   
instance IsSQLType a => IsSQLType (RowValue a) where sqlType = SQLRow sqlType


-- TODO: Pretty printer for SQL statements

data SQLSt (x :: SQLSem) a where
  Insert :: TableSpec -> QueryExpr -> SQLStatement () 
  -- Given a table and a query, insert those values into that table.

  Delete :: TableSpec -> ValueExpr -> SQLStatement () 
  -- Delete from a table those values specified by the predicate
 
  Update :: TableSpec -> ValueExpr -> [(Name, ValueExpr)] -> SQLStatement () 
  -- Same as above, this time taking two functions, the first is again the where
  -- clause, the 2nd computes the values to be updated. 

  SetRef :: Name -> ValueExpr -> SQLStatement () 
  -- Set the value of a reference to the given value. 

  NewRef :: SqlTType -> Maybe Name -> Maybe ValueExpr -> SQLStatement Name 
  -- Creates a new reference of the given type. Optionally takes a name to use
  -- as a prototype for the new name, and an initial value. The default initial
  -- value of the reference is null.

  MakeTable :: TableSpec -> SQLStatement () 
  DropTable :: TableSpec -> SQLStatement () 
  -- Create/dropping tables 

  IfSQL :: ValueExpr -> SQLStatement a -> SQLStatement a -> SQLStatement ()  
  -- An If statement takes a boolean valued expression. 
 
  (:>>=) :: IsSQLType a => SQLStatement a -> (a -> SQLSt x b) -> SQLSt x b 
  SQLRet :: IsSQLType a => a -> SQLSt x a 
  -- Semantics. Only allowed for sql types. 

  SQLFunCall :: SQLMethodName a -> VectorValue ValueExpr -> SQLStatement a
  SQLDefunMethod :: SQLMethod a -> SQLStatement (SQLMethodName a)
  -- Methods 

pattern SQLNoop :: SQLStatement () 
pattern SQLNoop = SQLRet () 

-- Convert a declaration to a table specification.
-- Based on Database.Design.Ampersand.FSpec.SQL.selectDeclaration
decl2TableSpec :: FSpec -> Declaration -> TableSpec
decl2TableSpec fSpec decl = 
  let q = QName . name 
      (plug,src,tgt) = 
        case decl of 
          Sgn{} -> getDeclarationTableInfo fSpec decl 
          Isn{} -> let (p,a) = getConceptTableInfo fSpec (detyp decl) in (p,a,a)
          Vs{}  -> error "decl2TableSpec: V[_,_] not expected here"
  in TableSpec (q plug) $ map q [src,tgt]

-- I really dont know if there is a better way in sql....
sqlTrue, sqlFalse :: ValueExpr
sqlTrue = BinOp (NumLit "0") ["="] (NumLit "0")
sqlFalse = BinOp (NumLit "0") ["="] (NumLit "1")

sqlNull :: ValueExpr 
sqlNull = SpecialOp ["NULL"] []

-- TODO: This function could do with some comments 
-- TODO: Test eca2SQL
-- TODO: Properly deal with the delta.. this will almost certainly not work.
-- TODO: Add an option to the ampersand executable which will print all of the 
--       eca rules and their corresponding SQL methods to stderr. 
eca2SQL :: FSpec -> ECArule -> SQLMethod ValueExpr 
eca2SQL fSpec@FSpec{originalContext,plugInfos} (ECA _ delta action _) = 
 SQLMethod "ecaRule" [Name deltaNm] $ 
  NewRef SQLBool (Just "checkDone") (Just sqlFalse) :>>= \nm -> 
  paClause2SQL action nm :>>= \_ -> 
  SQLRet (Iden [nm])
  
    where 
        -- TODO: Figure out how this plug stuff works... 
        deltaObj = Obj 
          { objnm = name delta, objpos = OriginUnknown, objctx = EDcD delta
          , objcrud = Cruds OriginUnknown (Just True) (Just True) (Just True) (Just True) 
          , objmsub = Nothing, objstrs = [], objmView = Nothing 
          }
        deltaPlug = makeUserDefinedSqlPlug originalContext deltaObj
        fSpec' = fSpec { plugInfos = InternalPlug deltaPlug : plugInfos } 
        expr2SQL' = expr2SQL fSpec' 

        done = \r -> SetRef r sqlTrue 
        notDone = const SQLNoop

        deltaNm = case delta of 
                    Sgn{} -> decnm delta 
                    _ -> error "eca2SQL: Got a delta which is not a parameter"
      
        paClause2SQL :: PAclause -> (Name -> SQLStatement ())
        paClause2SQL (Do Ins insInto toIns _motive) = \k -> 
          Insert (decl2TableSpec fSpec insInto) (expr2SQL' toIns) :>>= 
          const (done k) 
      
        paClause2SQL (Do Del delFrom toDel _motive) = 
          let sp@TableSpec{tableColumns = [src, tgt]} = decl2TableSpec fSpec delFrom
              srcE = Iden [src]; tgtE = Iden [tgt] 
              fromDelta = makeSelect { qeFrom = [ TRQueryExpr $ expr2SQL' toDel ] }
              dom = fromDelta { qeSelectList = [(srcE, Nothing)] }
              cod = fromDelta { qeSelectList = [(tgtE, Nothing)] }
              cond = BinOp (In True srcE $ InQueryExpr dom) ["AND"] (In True tgtE $ InQueryExpr cod)
          in \k -> Delete sp cond :>>= const (done k)
             
        paClause2SQL (Nop _motive) = done
        paClause2SQL (Blk _motive) = notDone

        paClause2SQL (CHC ps _motive) = \k -> 
          NewRef SQLBool (Just "checkDone") (Just sqlFalse) :>>= \checkDone -> 
          let fin = SetRef k (BinOp (Iden [k]) ["OR"] (Iden [checkDone])) in
          foldl (\doPs p -> paClause2SQL p checkDone :>>= \_ -> 
                            IfSQL (Iden [checkDone]) SQLNoop doPs 
                 ) fin ps 
          
        paClause2SQL (ALL ps _motive) = \k -> 
          NewRef SQLBool (Just "checkDone") Nothing :>>= \checkDone -> 
          foldl (\doPs p -> SetRef checkDone sqlFalse :>>= \_ -> 
                            paClause2SQL p checkDone :>>= \_ -> 
                            IfSQL (Iden [checkDone]) doPs SQLNoop
                ) (SetRef k (Iden[checkDone])) ps 

        paClause2SQL (GCH ps _motive) = \k -> 
          NewRef SQLBool (Just "checkDone") (Just sqlFalse) :>>= \checkDone -> 
          let fin = SetRef k (BinOp (Iden [k]) ["OR"] (Iden [checkDone])) in
          foldl (\doPs (neg, gr, p) -> 
                   let nneg = case neg of { Ins -> id; Del -> PrefixOp ["NOT"] } in 
                   IfSQL (nneg $ SubQueryExpr SqExists $ expr2SQL' gr) 
                     (paClause2SQL p checkDone :>>= \_ -> 
                      IfSQL (Iden [checkDone]) SQLNoop doPs
                     ) doPs
                 ) fin ps 

        paClause2SQL _ = error "paClause2SQL: unsupported operation" 
        {- 
        paClause2SQL (Let expr body _motive) = ???
        paClause2SQL (New typ go _motive) = 
          let tbl = decl2TableSpec fSpec (Isn typ)
          in \k -> Insert tbl (Values [ replicate (length $ tableColumns tbl) sqlNull ]) :>>= \_ -> 
                   ????
                   -- No clue. Need to clarify what this actually does. Every single function in all of ampersand 
                   -- throws an error at `Let' - so what the hell does it actually do?
        -}
