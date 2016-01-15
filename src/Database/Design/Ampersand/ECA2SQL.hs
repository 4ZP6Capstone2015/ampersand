{-# LANGUAGE PatternSynonyms, NoMonomorphismRestriction, OverloadedStrings, LambdaCase, RoleAnnotations, LiberalTypeSynonyms #-} 
{-# LANGUAGE ScopedTypeVariables #-} 
{-# OPTIONS -fno-warn-unticked-promoted-constructors #-} 

module Database.Design.Ampersand.ECA2SQL 
  ( module Database.Design.Ampersand.ECA2SQL
  ) where 

import Database.Design.Ampersand.Core.AbstractSyntaxTree 
  ( ECArule(..), PAclause(..), Expression(..), Declaration(..), AAtomValue(..), InsDel(..), Event(..)
  , A_Context(..), ObjectDef(..), ObjectDef(..), Origin(..), Cruds(..)
  )
import Database.Design.Ampersand.FSpec (FSpec(..)) 
import Language.SQL.SimpleSQL.Syntax 
  ( QueryExpr(..), ValueExpr(..), Name(..), TableRef(..), InPredValue(..), SubQueryExprType(..) 
  , makeSelect
  ) 
import Database.Design.Ampersand.FSpec.FSpec (PlugSQL(..), PlugInfo(..))
import Database.Design.Ampersand.FSpec.ToFSpec.ADL2Plug 
import Database.Design.Ampersand.FSpec.SQL (expr2SQL,prettySQLQuery) --added Bin,to,Pretty
import Database.Design.Ampersand.FSpec.FSpecAux (getDeclarationTableInfo,getConceptTableInfo)
import Database.Design.Ampersand.Basics (Named(..))
import Database.Design.Ampersand.Core.ParseTree (makePSingleton)
import Database.Design.Ampersand.ECA2SQL.Utils  
import Database.Design.Ampersand.ECA2SQL.TypedSQL 
import qualified Database.Design.Ampersand.ECA2SQL.TSQLCombinators as T 
import qualified GHC.TypeLits as TL 

-- TODO: Pretty printer for SQL statements
{- I believe these are all function declaration from 
the "A prettier printer"
- Philip Wadler
Can this be plugged in? 
-}

-- prettySQLQuery::FSpec -> Int -> Unique -> String -- not sure if this is right?
-- ^^ defined in SQL.hs.
-- we want to pretty print the SQL statements.
-- won't work.
-- pretty :: Int -> Doc -> String
-- (<>) :: Doc -> Doc -> Doc -> -- concatenates two documents, no format
-- group :: Doc -> Doc --returns set with one new element; defined by flatten, do we need this?
-- nil :: Doc -- left and right unit
-- text :: String -> Doc -- converts a string to the corresponding document
-- text concatText = case concatText of 
            -- (s ++ t) -> text s <> text table --homomorphism from string concat to doc concat, applied left to right
   -- "" -> nil
-- line :: Doc --line break, assume string passed to text has no line break
-- nest :: Int -> Doc -> Doc -- adds indentation to the document 
-- nest nestText = case nestText of  -- homomorph from addition to composition, distri through concat
   -- (i+j) x -> nest i (nest j x) -- applied left to right
   -- 0 x -> x -- applied left to right 
   -- (x <> y) -> nest i x <> nest i y -- applied right to left
   -- i nil -> nil -- ""
   -- i (text s) -> text s -- each law on a binary operator is paired with a corresponding law for its unit; right to left
-- layout :: Doc -> String --converts document to a string; identity function 
-- layout layoutText = case layoutText of
   -- (x <> y) -> layout x ++ layout y -- doc to string concat, layout is invert of text
   -- nil -> ""
   -- (text s) -> s
   -- (nest i line) -> '\n' : copy i '' -- layout of nested line is a newline followed by no indentation for lining up at each level
-- -- might want to take out tts and associated text
-- showTree showTreeText = case showTreeText of
   -- (Node s ts tts) -> text s <> nest (length s) (showBracket ts) <> nest (length s) (showBracket tts) -- can s = binSQLQuery (bceq0), ts = binSQLQuery (bceq1), or is s combineOp?
   -- (Node s ts nil) -> group (text s <> nest (length s) (showBracket ts)) -- keep total less than i character (pretty::Int -> Doc -> String)
-- showBracket stuff = 
   -- case stuff of [] -> nil
      -- ts -> text "INSERT INTO" <> nest 0 line showTrees ts <> text line "SELECT" <> nest 0 line showTree tts <> text line "FROM")
      -- [t] -> showTree t
      -- showTree (t:ts) -> showTree t <> line text "," <> showTree ts
   
   
-- -- INSERT INTO <tgt>
-- -- SELECT <src.col> --can this be binSQLQuery(bseSrc)? from SQL.hs ? - possibly, I'm still trying to figure that out
-- -- FROM <src> WHERE <condition> -- where = binSQLQuery (bseWhr)? -- not sure about the correctness of this query

-- -- text "INSERT INTO <tgt>" <> 
   -- -- nest 0 (
      -- -- line <> text "SELECT <src.col>"
      -- -- line <> text "FROM <src> " <> text "WHERE <condition>")



-- Convert a declaration to a table specification.
-- Based on Database.Design.Ampersand.FSpec.SQL.selectDeclaration
decl2TableSpec :: FSpec -> Declaration ->  TableSpec '[ "src" ::: 'SQLAtom, "tgt" ::: 'SQLAtom ]
decl2TableSpec fSpec decl = 
  let (plug,src,tgt) = 
        case decl of 
          Sgn{} -> getDeclarationTableInfo fSpec decl 
          Isn{} -> let (p,a) = getConceptTableInfo fSpec (detyp decl) in (p,a,a)
          Vs{}  -> error "decl2TableSpec: V[_,_] not expected here"
  in someTableSpecShape (QName $ name plug) (PCons (K (name src) :*: SSQLAtom) $ PCons (K (name tgt) :*: SSQLAtom) PNil) $
      \case { Dict -> \case { Refl -> \tbl -> TableAlias tbl }}

-- TODO: This function could do with some comments 
-- TODO: Test eca2SQL
-- TODO: Properly deal with the delta.. this will almost certainly not work.
-- TODO: Add an option to the ampersand executable which will print all of the 
--       eca rules and their corresponding SQL methods to stderr. 
-- TODO: Add the motives in comments to the generated code 

eca2SQL :: FSpec -> ECArule -> SQLMethod '[] 'SQLBool
eca2SQL fSpec@FSpec{originalContext,plugInfos} (ECA _ delta action _) =  
  MkSQLMethod $ \PNil -> 
    NewRef SSQLBool (Just "checkDone") (Just T.false) :>>= \checkDone -> 
    paClause2SQL action checkDone :>>= \_ -> 
    SQLRet (deref checkDone)
  
      where 
        -- TODO: Figure out how this plug stuff works... 
        deltaObj = Obj 
          { objnm = name delta, objpos = OriginUnknown, objctx = EDcD delta
          , objcrud = Cruds OriginUnknown (Just True) (Just True) (Just True) (Just True) 
          , objmsub = Nothing, objstrs = [], objmView = Nothing 
          }
        deltaPlug = makeUserDefinedSqlPlug originalContext deltaObj
        fSpec' = fSpec { plugInfos = InternalPlug deltaPlug : plugInfos } 
        expr2SQL' = expr2SQL fSpec'             -- calling expr2SQL function from SQL.hs
                                                -- returns a QueryExpr (for a select query)  
  
        done = \r -> SetRef r T.true  
        notDone = const SQLNoop

        -- TODO: Do something with the delta?
        _deltaNm = case delta of 
                    Sgn{} -> decnm delta        -- returns the name of the declaration 
                    _ -> error "eca2SQL: Got a delta which is not a parameter"
        
        paClause2SQL :: PAclause -> (SQLValRef 'SQLBool -> SQLStatement 'SQLUnit)

        paClause2SQL (Do Ins insInto toIns _motive) = \k ->                    -- PAClause case of Insert
          let tbl = decl2TableSpec fSpec insInto in 
          Insert tbl (unsafeSQLValFromQuery $ expr2SQL' toIns) :>>=            -- Insert :: TableSpec -> QueryExpr -> SQLStatement ()  
          const (done k)                                                       -- decl2TableSpec = fetch table specification
                                                                               -- expr2SQL = calls expr2SQL from SQL.hs, returns a QueryExpr for the toIns (Expression)


        paClause2SQL (Nop _motive) = done                                   -- PAClause case of Nop
        paClause2SQL (Blk _motive) = notDone                                -- PAClause case of Blk
                                                                            -- tells which expression from whichule has caused the blockage
                                                                            -- Ideally this case won't be reached in our project


        paClause2SQL (CHC ps _motive) = \k ->                               -- PAClause case of CHC; ps is the precisely one clause to be executed
          NewRef SSQLBool (Just "checkDone") (Just T.false) :>>= \checkDone -> 
          let fin = SetRef k (T.sql T.Or (deref checkDone) (deref k)) in
          foldl (\doPs p -> paClause2SQL  p checkDone :>>= \_ -> 
                            IfSQL (deref checkDone) SQLNoop doPs 
                 ) fin ps 

      
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
           
        paClause2SQL (ALL ps _motive) = \k ->                               -- PAClause case of ALL; all PAClauses are executed
          NewRef SSQLBool (Just "checkDone") Nothing :>>= \checkDone -> 
          foldl (\doPs p -> SetRef checkDone T.false :>>= \_ ->            -- sequential execution of all PAClauses
                            paClause2SQL p checkDone :>>= \_ -> 
                            IfSQL (deref checkDone) doPs SQLNoop
                ) (SetRef k (deref checkDone)) ps 
     
        -- guarded choice; The rule is maintained if one of the clauses of which the expression is populated is executed.
        paClause2SQL (GCH ps _motive) = \k ->                                    -- PAClause case of GHC
          NewRef SSQLBool (Just "checkDone") (Just T.false) :>>= \checkDone ->  
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

