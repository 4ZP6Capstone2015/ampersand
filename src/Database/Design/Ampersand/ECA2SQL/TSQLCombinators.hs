{-# LANGUAGE PatternSynonyms, NoMonomorphismRestriction, OverloadedStrings, LambdaCase, EmptyCase #-} 
{-# LANGUAGE TemplateHaskell, QuasiQuotes, ScopedTypeVariables, PolyKinds, UndecidableInstances, DataKinds, DefaultSignatures #-}
{-# OPTIONS -fno-warn-unticked-promoted-constructors #-} 

module Database.Design.Ampersand.ECA2SQL.TSQLCombinators
  ( module Database.Design.Ampersand.ECA2SQL.TSQLCombinators
  ) where 

import Database.Design.Ampersand.ECA2SQL.TypedSQL hiding (In)  
import Database.Design.Ampersand.ECA2SQL.Utils 
import qualified Language.SQL.SimpleSQL.Syntax as Sm 
import Prelude (Maybe(..), error, (.), id, undefined, ($), Bool(..), String, (++)) -- This module is intended to be imported qualified
import Control.Applicative (Applicative(..), (<$>))
import qualified GHC.TypeLits as TL 

true :: SQLVal 'SQLBool
true = sql PTrue 

false :: SQLVal 'SQLBool
false = sql PFalse 

not :: SQLVal 'SQLBool -> SQLVal 'SQLBool
not = sql Not 

in_, notIn :: forall a . SQLVal a -> SQLVal ('SQLRel a) -> SQLVal 'SQLBool
in_ = sql In; notIn = sql NotIn 

-- Indexing. Overloaded operator with typeclasses. 
class IndexInto (t :: SQLType) (indexk :: KProxy index) | t -> indexk where 
  type GetAtIndex t (i :: index) :: SQLType 
  (!) :: forall (i :: index) . SQLVal t -> SingT i -> SQLVal (GetAtIndex t i)  

instance IndexInto ('SQLRow xs) ('KProxy :: KProxy Symbol) where 
  type GetAtIndex ('SQLRow xs) (nm :: Symbol) = LookupRec xs nm 

  (!) v@(SQLQueryVal x) i@(SSymbol pri) = 
    let strNm = Sm.Name $ TL.symbolVal pri in 
    case typeOf v of { SSQLRow t -> 
    case lookupRec (sing2prod t) i of { r -> 
    withSingT r $ \_ ->  
      case isScalarType r of 
        STrue -> SQLScalarVal $ 
          case x of 
            Sm.Table ns -> Sm.Iden (ns++[strNm])
            _ -> Sm.SubQueryExpr Sm.SqSq $ Sm.makeSelect 
                   { qeSetQuantifier = Sm.All 
                   , qeSelectList    = [ (Sm.Iden [strNm], Nothing) ] 
                   , qeFrom          = [ Sm.TRQueryExpr x ]
                   } 
        SFalse -> SQLQueryVal $ Sm.makeSelect 
                   { qeSetQuantifier = Sm.All 
                   , qeSelectList    = [ (Sm.Iden [strNm], Nothing) ] 
                   , qeFrom          = [ Sm.TRQueryExpr x ]
                   } 
     }}
  (!) _ _ = error "IndexInto{SQLRow}(!):impossible"

instance IndexInto ('SQLRel ('SQLRow xs)) ('KProxy :: KProxy Symbol) where 
  type GetAtIndex ('SQLRel ('SQLRow xs)) (nm :: Symbol) = 'SQLRel (LookupRec xs nm)

instance IndexInto ('SQLVec x) ('KProxy :: KProxy TL.Nat) where 
  type GetAtIndex ('SQLVec ts) (i :: TL.Nat) = LookupIx ts i

-- Primitive functions go here. This allows an implementation of SQL to be 
-- as simple as a function of type the same as `primSQL'. 
data PrimSQLFunction (args :: [SQLType]) (out :: SQLType) where 
  PTrue, PFalse :: PrimSQLFunction '[] 'SQLBool 
  Not :: PrimSQLFunction '[ 'SQLBool ] 'SQLBool
  Or, And :: PrimSQLFunction '[ 'SQLBool, 'SQLBool ] 'SQLBool
  In, NotIn :: PrimSQLFunction '[ a, 'SQLRel a ] 'SQLBool
  Exists :: PrimSQLFunction '[ 'SQLRel a ] 'SQLBool 

primSQL :: PrimSQLFunction args out -> Prod SQLVal args -> SQLVal out 
primSQL PTrue = \PNil -> SQLScalarVal $ Sm.In True (Sm.NumLit "0") $ Sm.InList [Sm.NumLit "0"]
primSQL PFalse = \PNil -> SQLScalarVal $ Sm.In True (Sm.NumLit "1") $ Sm.InList [Sm.NumLit "0"]
primSQL Not = \(SQLScalarVal x :> PNil) -> SQLScalarVal $ Sm.PrefixOp ["NOT"] x 
primSQL In = \(SQLScalarVal x :> SQLQueryVal y :> PNil) -> SQLScalarVal $ Sm.In True x (Sm.InQueryExpr y) 
primSQL NotIn = \(SQLScalarVal x :> SQLQueryVal y :> PNil) -> SQLScalarVal $ Sm.In False x (Sm.InQueryExpr y) 
primSQL Or = \(SQLScalarVal x :> SQLScalarVal y :> PNil) -> SQLScalarVal $ Sm.BinOp x ["OR"] y
primSQL And = \(SQLScalarVal x :> SQLScalarVal y :> PNil) -> SQLScalarVal $ Sm.BinOp x ["AND"] y
primSQL Exists = \(SQLQueryVal x :> PNil) -> SQLScalarVal $ Sm.SubQueryExpr Sm.SqExists x 

sql :: (Uncurry SQLVal args out fun) => PrimSQLFunction args out -> fun 
sql fun = uncurryN $ primSQL fun 


{-
-- The type of select is much too complex...

data Aliased t where 
  NoAlias :: SQLVal t -> Aliased (nm ::: t) 
  Alias   :: SQLVal t -> SingT nm -> Aliased (nm ::: t) 

newtype Table t = MkTable { tableRows :: SQLVal ('SQLRel ('SQLRow t)) }

data SortSpec t = SortSpec (SQLVal t) Direction NullsOrder

select :: Sm.SetQuantifier                                        -- Quantifier     [DISTINCT,ALL] 
       -> Prod Aliased out_ts                                     -- Select list    ( <expr> [as col], ... )
       -> Prod Table src_ts                                       -- Source tables  ( can be almost anything )
       -> Maybe (SQLVal 'SQLBool)                                 -- WHERE clause   ( [ WHERE <expr> ] )
       -> Maybe (SQLVal 'SQLBool)                                 -- HAVING clause  ( [ HAVING <expr> ] )
       -> 
-}
