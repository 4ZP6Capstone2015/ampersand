{-# LANGUAGE PatternSynonyms, NoMonomorphismRestriction, OverloadedStrings, LambdaCase, RoleAnnotations, LiberalTypeSynonyms #-} 
{-# LANGUAGE ScopedTypeVariables #-} 
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
import Database.Design.Ampersand.FSpec.FSpecAux (getDeclarationTableInfo,getConceptTableInfo)
import Database.Design.Ampersand.Basics (Named(..))
import Database.Design.Ampersand.Core.ParseTree (makePSingleton)
import Database.Design.Ampersand.ECA2SQL.Utils  
import Database.Design.Ampersand.ECA2SQL.TypedSQL 
import Database.Design.Ampersand.Basics.Assertion
import qualified Database.Design.Ampersand.ECA2SQL.TSQLCombinators as T 
import qualified GHC.TypeLits as TL 
import Database.Design.Ampersand.ECA2SQL.Singletons

-- Convert a declaration to a table specification.
-- Based on Database.Design.Ampersand.FSpec.SQL.selectDeclaration
decl2TableSpec :: FSpec -> Declaration 
               -> (forall k i j . TableSpec k -> i `Elem` k -> j `Elem` k -> r) 
               -> r 
decl2TableSpec fSpec decl k = 
  case getDeclarationTableInfo fSpec decl of 
    (plug, srcAtt, tgtAtt) -> 
      case plug of 
        TblSQL{} -> undefined
        BinSQL{} -> undefined
        ScalarSQL{} -> impossible "ScalarSQL unexecpted here" () 


mkInsDelAtom :: FSpec -> Declaration -> Ins ->  

-- (forall tbl i j . TableSpec tbl -> i `Elem` tbl -> j `Elem` tbl -> 

-- decl2TableSpec fSpec decl = 
--   let (plug,src,tgt) = 
--         case decl of 
--           Sgn{} -> case getDeclarationTableInfo fSpec decl of { (p,a,b) -> (p,name a,name b) }
--           Isn{} -> let (p,a) = getConceptTableInfo fSpec (detyp decl) 
--                    in (p,name a, freshName (name a) 1)
                    
--           Vs{}  -> error "decl2TableSpec: V[_,_] not expected here"
--   in tableSpec' (Name Nothing $ name plug) ((K src :*: SingT WSQLAtom) :> (K tgt :*: SingT WSQLAtom) :> PNil) $ \case 
--        Just (Refl,tb) -> TableAlias_ (sing :: SingT '[ "src", "tgt" ]) tb 
--        Nothing -> error $ "decl2TableSpec: declaration did not produce unique table spec:\n" 
--                     ++ show (src, tgt) 

-- TODO: This function could do with some comments 
-- TODO: Test eca2SQL
-- TODO: Properly deal with the delta.. this will almost certainly not work.
-- TODO: Add an option to the ampersand executable which will print all of the 
--       eca rules and their corresponding SQL methods to stderr. 
-- TODO: Add the motives in comments to the generated code 

eca2SQL :: FSpec -> ECArule -> SQLMethod '[] 'SQLBool
eca2SQL fSpec@FSpec{plugInfos=_plugInfos} (ECA _ delta action _) =  
  MkSQLMethod sing $ \PNil -> 
    NewRef sing (Just "checkDone") (Just T.false) :>>= \checkDone -> 
    paClause2SQL action checkDone :>>= \_ -> 
    SQLRet (deref checkDone)
  
      where 
        -- renameECA :: Declaration -> ECArule -> ECArule 

        -- -- TODO: Figure out how this plug stuff works... 
        -- deltaCtx = case delta of 
        --             Sgn{decsgn = Sign a _} -> EDcI a -- ???? 
        --             Isn{detyp} -> EDcI detyp
        --             _ -> error "eca2SQL/deltaCtx:???"
                     
        -- deltaObj = Obj 
        --   { objnm = name delta, objpos = OriginUnknown, objctx = deltaCtx 
        --   , objcrud = Cruds OriginUnknown (Just True) (Just True) (Just True) (Just True) 
        --   , objmsub = Nothing, objstrs = [], objmView = Nothing 
        --   }
        -- deltaPlug = makeUserDefinedSqlPlug originalContext deltaObj
        -- deltaPlug = BinSQL 
        --   { sqlname = name delta 
        --   , columns = ( Att { attName = "src" 
        --                     , attExpr = EDcD delta    
        --                     , attType = SQLVarchar 255 
        --                     , attUse  = PlainAttr
        --                     , attNull = True
        --                     , attUniq = True }
        --               , Att { attName = "tgt" 
        --                     , attExpr = EDcD delta    
        --                     , attType = SQLVarchar 255 
        --                     , attUse  = PlainAttr
        --                     , attNull = True
        --                     , attUniq = True }
        --               )
        --   , cLkpTbl = [] --  ??? [(A_Concept, SqlAttribute)]
        --   , mLkp = EDcD delta -- :: Expression
        --   }

        -- fSpec' = fSpec { plugInfos = InternalPlug deltaPlug : plugInfos } 

        expr2SQL' = expr2SQL fSpec              -- calling expr2SQL function from SQL.hs
                                                -- returns a QueryExpr (for a select query)  
  
        done = \r -> SetRef r T.true  
        notDone = const SQLNoop

        -- TODO: Do something with the delta?
        _deltaNm = case delta of 
                    Sgn{} -> decnm delta        -- returns the name of the declaration 
                    _ -> error "eca2SQL: Got a delta which is not a parameter"
        
        paClause2SQL :: PAclause -> SQLValRef 'SQLBool -> SQLStatement 'SQLUnit
{-
        paClause2SQL (Do Ins insInto toIns _motive) = \k ->                    -- PAClause case of Insert
          let tbl = decl2TableSpec fSpec insInto in 
          Insert tbl (unsafeSQLValFromQuery $ expr2SQL' toIns) :>>=            -- Insert :: TableSpec -> QueryExpr -> SQLStatement ()  
          const (done k)                                                       -- decl2TableSpec = fetch table specification
                                                                               -- expr2SQL = calls expr2SQL from SQL.hs, returns a QueryExpr for the toIns (Expression)

-}
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

      {-
        paClause2SQL (Do Del delFrom toDel _motive) =                       -- PAClause case of Delete
          let tbl = decl2TableSpec fSpec delFrom
              -- This needs a type annotation because it is unsafe
              toDelExpr :: SQLVal ('SQLRel ('SQLRow '[ "src" ::: 'SQLAtom, "tgt" ::: 'SQLAtom ] ))
              toDelExpr = unsafeSQLValFromQuery (expr2SQL' toDel)
              src = sing :: SingT "src" 
              tgt = sing :: SingT "tgt" 
              dom = toDelExpr T.! src 
              cod = toDelExpr T.! tgt 
              cond = \tup -> T.sql T.And (T.in_ (tup T.! src) dom) (T.in_ (tup T.! tgt) cod)
          in \k -> Delete tbl cond :>>= const (done k) 
-}           

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
        {- 
        paClause2SQL (Let expr body _motive) = ???
        paClause2SQL (New typ go _motive) = 
          let tbl = decl2TableSpec fSpec (Isn typ)
          in \k -> Insert tbl (Values [ replicate (length $ tableColumns tbl) sqlNull ]) :>>= \_ -> 
                   ????
                   -- No clue. Need to clarify what this actually does. Every single function in all of ampersand 
                   -- throws an error at `Let' - so what the hell does it actually do?
        -}

