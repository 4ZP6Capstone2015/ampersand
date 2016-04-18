{-# LANGUAGE PatternSynonyms, NoMonomorphismRestriction, OverloadedStrings, LambdaCase, RoleAnnotations, LiberalTypeSynonyms #-} 
{-# LANGUAGE ScopedTypeVariables, ViewPatterns #-} 
{-# OPTIONS -fno-warn-unticked-promoted-constructors #-} 

module Database.Design.Ampersand.ECA2SQL 
  ( module Database.Design.Ampersand.ECA2SQL
  ) where 

import Database.Design.Ampersand.Core.AbstractSyntaxTree 
  ( ECArule(..), PAclause(..), Expression(..), Declaration(..), AAtomValue(..), InsDel(..), Event(..)
  , A_Context(..), ObjectDef(..), ObjectDef(..), Origin(..), Cruds(..), Signature(..) 
  )
import Database.Design.Ampersand.FSpec (FSpec(..)) 
import Language.SQL.SimpleSQL.Syntax 
  ( QueryExpr(..), ValueExpr(..), Name(..), TableRef(..), InPredValue(..), SubQueryExprType(..) 
  , makeSelect
  ) 
import Database.Design.Ampersand.FSpec.FSpec (PlugSQL(..), PlugInfo(..), SqlAttribute(..), SqlAttributeUsage(..), SqlTType(SQLVarchar))
import Database.Design.Ampersand.FSpec.ToFSpec.ADL2Plug 
import Database.Design.Ampersand.FSpec.SQL (expr2SQL,prettySQLQuery) --added Bin,to,Pretty
import qualified Database.Design.Ampersand.FSpec.SQL as FSpec
import Database.Design.Ampersand.FSpec.FSpecAux (getDeclarationTableInfo,getConceptTableInfo)
import Database.Design.Ampersand.Basics (Named(..))
import Database.Design.Ampersand.Core.ParseTree (makePSingleton)
import Database.Design.Ampersand.ECA2SQL.Utils  
import Database.Design.Ampersand.ECA2SQL.TypedSQL 
import Database.Design.Ampersand.Basics.Assertion
import Database.Design.Ampersand.Basics.Version 
import qualified Database.Design.Ampersand.ECA2SQL.TSQLCombinators as T 
import qualified GHC.TypeLits as TL 
import Database.Design.Ampersand.ECA2SQL.Singletons

-- Convert a declaration to a table specification.
-- Based on Database.Design.Ampersand.FSpec.SQL.selectDeclaration

-- decl2TableSpec :: FSpec -> Declaration 
--                -> (forall k i j . TableSpec k -> i `Elem` k -> j `Elem` k -> r) 
--                -> r 
-- decl2TableSpec fSpec decl k = 
--   case getDeclarationTableInfo fSpec decl of 
--     (plug, srcAtt, tgtAtt) -> 
--       case plug of 
--         TblSQL{} -> undefined
--         BinSQL{} -> undefined
--         ScalarSQL{} -> impossible "ScalarSQL unexecpted here" () 


unsafeMkInsDelAtom :: FSpec -> Declaration -> InsDel -> Expression -> SQLStatement 'SQLUnit 
unsafeMkInsDelAtom fSpec decl =
  case getDeclarationTableInfo fSpec decl of 
    (plug, srcAtt, tgtAtt) ->  
      case plug of 
        TblSQL{} -> fatal 0 "TblSQL currently unsupported in ECA2SQL" 
        BinSQL{} -> 
          case someTableSpec (fromString $ sqlname plug) 
                 [ (fromString $ attName srcAtt, Ex (sing :: SQLTypeS 'SQLAtom)) 
                 , (fromString $ attName tgtAtt, Ex (sing :: SQLTypeS 'SQLAtom)) 
                 ] of 
            Nothing -> fatal 0 $ unwords 
                        [ "Could not construct table spec from attributes\n", 
                        show srcAtt, " and ", show tgtAtt ] 
            Just (Ex (tbl :: TableSpec tbl)) -> \act toInsDel -> 
              case act of 
                Ins -> withSingT (typeOfTableSpec tbl) $ \(singFromProxy -> SingT (WSQLRow{})) -> 
                         Insert tbl (unsafeSQLValFromQuery $ expr2SQL fSpec toInsDel)
                         
                Del -> 
                  let toDelExpr :: SQLVal ('SQLRel ('SQLRow '[ "src" ::: 'SQLAtom, "tgt" ::: 'SQLAtom ] ))
                      toDelExpr = unsafeSQLValFromQuery $ expr2SQL fSpec toInsDel
                      src = sing :: SingT "src" 
                      tgt = sing :: SingT "tgt" 
                      dom = toDelExpr T.! src 
                      cod = toDelExpr T.! tgt 

                      cond :: SQLVal ('SQLRow '[ "src" ::: 'SQLAtom, "tgt" ::: 'SQLAtom ] ) -> SQLVal 'SQLBool 
                      cond = \tup -> T.sql T.And (T.in_ (tup T.! src) dom) (T.in_ (tup T.! tgt) cod)

                      -- Unsafely recasting the type of `cond' 
                      cond' :: SQLVal ('SQLRow tbl) -> SQLVal 'SQLBool 
                      cond' = \(SQLQueryVal x) -> cond (SQLQueryVal x) 

                  in Delete tbl cond' 
                      

        ScalarSQL{} -> fatal 0 "ScalarSQL unexecpted here" 
    
unsafeDeclToTbl :: FSpec -> Declaration -> (forall (xs :: [SQLType]) . Prod SingT xs -> r) -> r 
unsafeDeclToTbl = error "TODO"  


eca2SQL :: FSpec -> ECArule -> (forall k . SQLMethod k 'SQLBool -> r) -> r
eca2SQL fSpec@FSpec{plugInfos=_plugInfos} (ECA (On _insDel _ruleDecl) delta action _) q = q $ 
  unsafeDeclToTbl fSpec _ruleDecl $ \argsT -> 
  MkSQLMethod argsT $ \_args -> 
    let expr2SQL' = FSpec.expr2SQL' (\case 
                      "Delta" -> Just $ error "TODO" 
                      _ -> Nothing
                      ) fSpec             
        -- calling expr2SQL function from SQL.hs
        -- returns a QueryExpr (for a select query)  
  
        done = \r -> SetRef r T.true  
        notDone = const SQLNoop
        
        paClause2SQL :: PAclause -> SQLValRef 'SQLBool -> SQLStatement 'SQLUnit
        paClause2SQL (Do insDel' tgtTbl tgtExpr _motive) = \k -> 
          unsafeMkInsDelAtom fSpec tgtTbl insDel' tgtExpr :>>= \_ -> 
          done k 

        paClause2SQL (Nop _motive) = done                                   -- PAClause case of Nop
        paClause2SQL (Blk _motive) = notDone                                -- PAClause case of Blk
                                                                            -- tells which expression from whichule has caused the blockage
                                                                            -- Ideally this case won't be reached in our project


        paClause2SQL (CHC ps _motive) = \k ->                               -- PAClause case of CHC; ps is the precisely one clause to be executed
          NewRef sing (Just "checkDone") (Just T.false) :>>= \checkDone -> 
          let fin = SetRef k (T.sql T.Or (deref checkDone) (deref k)) in
          foldl (\doPs p -> paClause2SQL  p checkDone :>>= \_ -> 
                            IfSQL (deref checkDone) SQLNoop doPs 
                 ) fin ps 

        paClause2SQL (ALL ps _motive) = \k ->                               -- PAClause case of ALL; all PAClauses are executed
          NewRef sing (Just "checkDone") Nothing :>>= \checkDone -> 
          foldl (\doPs p -> SetRef checkDone T.false :>>= \_ ->            -- sequential execution of all PAClauses
                            paClause2SQL p checkDone :>>= \_ -> 
                            IfSQL (deref checkDone) doPs SQLNoop
                ) (SetRef k (deref checkDone)) ps 
     
        -- guarded choice; The rule is maintained if one of the clauses of which the expression is populated is executed.
        paClause2SQL (GCH ps _motive) = \k ->                                    -- PAClause case of GHC
          NewRef sing (Just "checkDone") (Just T.false) :>>= \checkDone ->  
          let fin = SetRef k (T.sql T.Or (deref checkDone) (deref k)) in
          foldl (\doPs (neg, gr, p) -> 
                   let nneg = case neg of { Ins -> id; Del -> T.sql T.Not } 
                       guardExpr = unsafeSQLValFromQuery $ expr2SQL' gr
                       guardExpr :: SQLVal ('SQLRel ('SQLRow '[ "dummy" ::: 'SQLAtom ]))
                       -- we don't actually know the type of the guard expression, other than it is a relation.
                   in 
                   IfSQL (nneg $ T.sql T.Exists guardExpr) 
                     (paClause2SQL p checkDone :>>= \_ -> 
                      IfSQL (deref checkDone) SQLNoop doPs
                     ) doPs
                 ) fin ps 
      
        paClause2SQL _ = error "paClause2SQL: unsupported operation" 
    in 
      NewRef sing (Just "checkDone") (Just T.false) :>>= \checkDone -> 
      paClause2SQL action checkDone :>>= \_ -> 
      SQLRet (deref checkDone)
