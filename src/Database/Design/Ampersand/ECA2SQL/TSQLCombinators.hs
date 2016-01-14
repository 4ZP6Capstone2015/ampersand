{-# LANGUAGE PatternSynonyms, NoMonomorphismRestriction, OverloadedStrings, LambdaCase, EmptyCase #-} 
{-# LANGUAGE TemplateHaskell, QuasiQuotes, ScopedTypeVariables, PolyKinds, UndecidableInstances, DataKinds, DefaultSignatures #-}
{-# OPTIONS -fno-warn-unticked-promoted-constructors -fno-warn-incomplete-patterns #-} 

module Database.Design.Ampersand.ECA2SQL.TSQLCombinators
  ( module Database.Design.Ampersand.ECA2SQL.TSQLCombinators
  ) where 

import Database.Design.Ampersand.ECA2SQL.TypedSQL 
import Database.Design.Ampersand.ECA2SQL.Utils 
import qualified Language.SQL.SimpleSQL.Syntax as Sm 
import Prelude (Maybe(..), error, (.), id, undefined, ($), Bool(..)) -- This module is intended to be imported qualified
import Control.Applicative (Applicative(..), (<$>))

true :: SQLVal 'SQLBool
true = SQLScalarVal $ Sm.In True (Sm.NumLit "0") $ Sm.InList [Sm.NumLit "0"]

false :: SQLVal 'SQLBool
false = SQLScalarVal $ Sm.In True (Sm.NumLit "1") $ Sm.InList [Sm.NumLit "0"]

not :: SQLVal 'SQLBool -> SQLVal 'SQLBool
not (SQLScalarVal x) = SQLScalarVal $ Sm.PrefixOp ["NOT"] x 

in_, notIn :: forall a . (IsScalarType a ~ True) => SQLVal a -> SQLVal ('SQLRel a) -> SQLVal 'SQLBool
in_ (SQLScalarVal x) (SQLQueryVal y) = SQLScalarVal $ Sm.In True x (Sm.InQueryExpr y) 
notIn (SQLScalarVal x) (SQLQueryVal y) = SQLScalarVal $ Sm.In False x (Sm.InQueryExpr y) 

type family ProjRows (xs :: [RecLabel Symbol SQLType]) :: [RecLabel Symbol SQLType] where 
  ProjRows '[] = '[] 
  ProjRows ((nm ::: ty) ': ts) = (nm ::: 'SQLRel ty) ': ProjRows ts 

-- Prooj obligations... ugh. I would really love to replace this with `unsafeCoerce'.
proj_is_vtr :: forall (ts :: [RecLabel Symbol SQLType]) . (NonEmpty ts) => Prod SingT ts
            -> (IsScalarType (ProjRows ts) :~: False, Prod SingT (ProjRows ts), Dict (NonEmpty (ProjRows ts)))
proj_is_vtr (PCons (SRecLabel nm x) PNil) = (Refl, PCons (SRecLabel nm (SSQLRel x)) PNil , Dict)
proj_is_vtr (PCons (SRecLabel nm x) xs@PCons{}) =
  case proj_is_vtr xs of
    (Refl, pr, Dict) -> (Refl, PCons (SRecLabel nm $ SSQLRel x) pr, Dict)

proj_is_vtr _ = error "proj_is_vtr:impossible"

-- Given an expression representing some relational value, returns a row of expressions
-- representing that same value. 
project :: forall ts . (NonEmpty ts) => SQLVal ('SQLRel ('SQLRow ts)) -> SQLVal ('SQLRow (ProjRows ts))
project v0@(SQLQueryVal x) = 
  case typeOf v0 of { SSQLRel (SSQLRow t) -> 
  case proj_is_vtr t of { (Refl, ts', Dict) -> 
  withSingT (SSQLRow ts') $ SQLQueryVal x -- TODO: is this really correct?
  }}


-- Indexing a row 
type Attr = (SingT :: Symbol -> *) 

-- (!) :: (Lookup xs nm ~ r) => SQLVal ('SQLRow xs) -> SingT nm -> SQLVal r
-- x ! t@(SSymbol tp) =  $ Sm.makeSelect 
--   { Sm.qeSelectList = [ (Sm.Iden [ Sm.Name $ symbolVal tp ], Nothing) ]
--   , Sm.qeFrom = [ Sm.TRQueryExpr $ primValOf x ]
--   , Sm.qeSetQuantifier = Sm.All 
--   } 
