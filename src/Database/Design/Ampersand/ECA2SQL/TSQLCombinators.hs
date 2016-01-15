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
import qualified GHC.TypeLits as TL 

true :: SQLVal 'SQLBool
true = SQLScalarVal $ Sm.In True (Sm.NumLit "0") $ Sm.InList [Sm.NumLit "0"]

false :: SQLVal 'SQLBool
false = SQLScalarVal $ Sm.In True (Sm.NumLit "1") $ Sm.InList [Sm.NumLit "0"]

not :: SQLVal 'SQLBool -> SQLVal 'SQLBool
not (SQLScalarVal x) = SQLScalarVal $ Sm.PrefixOp ["NOT"] x 

in_, notIn :: forall a . (IsScalarType a ~ True) => SQLVal a -> SQLVal ('SQLRel a) -> SQLVal 'SQLBool
in_ (SQLScalarVal x) (SQLQueryVal y) = SQLScalarVal $ Sm.In True x (Sm.InQueryExpr y) 
notIn (SQLScalarVal x) (SQLQueryVal y) = SQLScalarVal $ Sm.In False x (Sm.InQueryExpr y) 

{-
type family ProjRows (xs :: [RecLabel Symbol SQLType]) :: [RecLabel Symbol SQLType] where 
  ProjRows '[] = '[] 
  ProjRows ((nm ::: ty) ': ts) = (nm ::: 'SQLRel ty) ': ProjRows ts 

-- Prooj obligations... ugh. I would really love to replace this with `unsafeCoerce'.
proj_is_vtr :: forall (ts :: [RecLabel Symbol SQLType]) . (NonEmpty ts) => Prod SingT ts
            -> (Prod SingT (ProjRows ts), Dict (NonEmpty (ProjRows ts)))
proj_is_vtr (PCons (SRecLabel nm x) PNil) = (PCons (SRecLabel nm (SSQLRel x)) PNil , Dict)
proj_is_vtr (PCons (SRecLabel nm x) xs@PCons{}) =
  case proj_is_vtr xs of
    (pr, Dict) -> (PCons (SRecLabel nm $ SSQLRel x) pr, Dict)

proj_is_vtr _ = error "proj_is_vtr:impossible"
-}

-- Indexing. Overloaded operator with typeclasses. 

class IndexInto (t :: SQLType) (indexk :: KProxy index) | t -> indexk where 
  type GetAtIndex t (i :: index) :: SQLType 
  (!) :: SQLVal t -> SingT i -> SQLVal (GetAtIndex t i)  

instance IndexInto ('SQLRow xs) ('KProxy :: KProxy Symbol) where 
  type GetAtIndex ('SQLRow xs) (nm :: Symbol) = Lookup xs nm 

instance IndexInto ('SQLRel ('SQLRow xs)) ('KProxy :: KProxy Symbol) where 
  type GetAtIndex ('SQLRel ('SQLRow xs)) (nm :: Symbol) = 'SQLRel (Lookup xs nm)

instance IndexInto ('SQLVec x) ('KProxy :: KProxy TL.Nat) where 
  type GetAtIndex ('SQLVec ts) (i :: TL.Nat) = Lookup ts i



-- (!) :: (Lookup xs nm ~ r) => SQLVal ('SQLRow xs) -> SingT nm -> SQLVal r
-- x ! t@(SSymbol tp) =  $ Sm.makeSelect 
--   { Sm.qeSelectList = [ (Sm.Iden [ Sm.Name $ symbolVal tp ], Nothing) ]
--   , Sm.qeFrom = [ Sm.TRQueryExpr $ primValOf x ]
--   , Sm.qeSetQuantifier = Sm.All 
--   } 
