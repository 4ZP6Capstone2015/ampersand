{-# LANGUAGE PatternSynonyms, NoMonomorphismRestriction, OverloadedStrings, LambdaCase, EmptyCase #-} 
{-# LANGUAGE TemplateHaskell, QuasiQuotes, ScopedTypeVariables, PolyKinds, UndecidableInstances, DataKinds, DefaultSignatures #-}
{-# OPTIONS -fno-warn-unticked-promoted-constructors #-} 

module Database.Design.Ampersand.ECA2SQL.TypedSQL 
  ( module Database.Design.Ampersand.ECA2SQL.TypedSQL
  ) where 

import Database.Design.Ampersand.Core.AbstractSyntaxTree 
  ( 
   -- ECArule(..), PAclause(..)
  -- Expression(..), Declaration(..), AAtomValue(..), InsDel(..), Event(..)
   -- A_Context(..), ObjectDef(..), ObjectDef(..), Origin(..), Cruds(..)
  )

import Control.Applicative
import qualified Language.SQL.SimpleSQL.Syntax as Sm 
import Language.SQL.SimpleSQL.Syntax (ValueExpr(..), QueryExpr(..), TableRef(..), Name(..))  
import Data.Proxy (Proxy(..), KProxy(..))
import qualified GHC.TypeLits as TL 
import GHC.TypeLits (Symbol)
import GHC.Exts (Constraint)
import Data.Type.Equality ((:~:)(..))

-- Basic model SQL types represented in Haskell 

-- Generic combinators 
data Prod (f :: k -> *) (xs :: [k]) where 
  PNil :: Prod f '[] 
  PCons :: f x -> Prod f xs -> Prod f (x ': xs) 

data Sum (f :: k -> *) (xs :: [k]) where 
  SHere :: f x -> Sum f (x ': xs) 
  SThere :: Sum f xs -> Sum f (x ': xs) 

class All (c :: k -> Constraint) (xs :: [k]) where   
  mkProdC :: Proxy c -> (forall a . c a => p a) -> Prod p xs 

instance All (c :: k -> Constraint) '[] where mkProdC _ _ = PNil 
instance (All c xs, c x) => All c (x ': xs) where mkProdC pr k = PCons k (mkProdC pr k) 

cong :: f :~: g -> a :~: b -> f a :~: g b 
cong Refl Refl = Refl 

cong' :: f a :~: f b -> a :~: b 
cong' Refl = Refl 

cong2 :: f :~: g -> a :~: a' -> b :~: b' -> f a b :~: g a' b' 
cong2 Refl Refl Refl = Refl 

cong3 :: f :~: g -> a :~: a' -> b :~: b' -> c :~: c' -> f a b c :~: g a' b' c' 
cong3 Refl Refl Refl Refl = Refl 


newtype Elem (x :: k) (xs :: [k]) = MkElem { getElem :: Sum ((:~:) x) xs }

data AppliedTo (x :: k) (f :: k -> *) where Ap :: f x -> x `AppliedTo` f 

newtype Id a = Id { unId :: a }
newtype (:.:) (f :: k1 -> *) (g :: k0 -> k1) (a :: k0) = Cmp { unCmp :: f (g a) } 

type ($) f a = f a 

-- Decidable equality 
class DecideEq (f :: k -> *) where 
  (%==) :: forall x y . f x -> f y -> Maybe (x :~: y) 

decideSum :: (forall q  . Elem q set -> f q -> g q -> Maybe (f :~: g)) -> Sum f set -> Sum g set -> Maybe (f :~: g) 
decideSum = undefined  

instance (DecideEq f) => DecideEq (Prod f) where 
  PNil %== PNil = Just Refl 
  PCons x xs %== PCons y ys = liftA2 (cong2 Refl) (x %== y) (xs %== ys) 
  _ %== _ = Nothing 

instance DecideEq (SingT :: Nat -> *) where 
  SZ %== SZ = Just Refl 
  SS n %== SS m = fmap (cong Refl) $ n %== m 
  _ %== _ = Nothing 

instance DecideEq (SingT :: Symbol -> *) where 
  SSymbol s0 %== SSymbol s1 = TL.sameSymbol s0 s1 

-- Generic singleton indexed on kind
data family SingT (y :: k) 

class Sing x where 
  sing :: SingT x 

-- Symbol
data instance SingT (y :: Symbol) where 
  SSymbol :: TL.KnownSymbol x => Proxy x -> SingT x 
type SymbolSing = (SingT :: Symbol -> *)
instance TL.KnownSymbol x => Sing x where 
  sing = SSymbol Proxy 

-- Nat 
data instance SingT (y :: Nat) where 
  SZ :: SingT 'Z 
  SS :: SingT n -> SingT ('S n) 
type NatSing = (SingT :: Nat -> *)
instance Sing 'Z where sing = SZ 
instance Sing n => Sing ('S n) where sing = SS sing 

data Nat = Z | S Nat 

-- SQL Types 

data RecLabel a b = a ::: b
data SQLType 
  = SQLAtom                            -- All scalar types. Should be split into the different types it represents 
  | SQLBool
  | SQLRow [RecLabel Symbol SQLType]   -- A table or row
  | SQLVec [SQLType]                   -- Essentially an unnamed row 

-- SQL types along with types in domain of interpretation 
data SQLRefType 
  = Ty SQLType 
  | SQLRef SQLType 
  | SQLUnit 
  | SQLMethod Symbol [SQLType] SQLType 

type SQLRow xs = 'Ty ('SQLRow xs) 
type SQLVec xs = 'Ty ('SQLVec xs) 
type SQLAtom = 'Ty 'SQLAtom 
type SQLBool = 'Ty 'SQLBool 

data instance SingT (x :: RecLabel a b) where 
  SRecLabel :: SingT a -> SingT b -> SingT (a ::: b) 

type SQLTypeS = (SingT :: SQLType -> *) 
newtype instance SingT (x :: SQLType) = SQLSing { getSQLSing :: SQLValProto () () x }
  
instance (Sing a, Sing b) => Sing (a ::: b) where sing = SRecLabel sing sing 
instance (All Sing xs) => Sing ('SQLRow xs) where sing = SQLSing $ SSQLRow () (mkProdC (Proxy :: Proxy Sing) sing) 
instance (All Sing xs) => Sing ('SQLVec xs) where sing = SQLSing $ SSQLVec () (mkProdC (Proxy :: Proxy Sing) sing) 
instance Sing 'SQLAtom where sing = SQLSing $ SSQLAtom ()

-- A reference to a SQL value. Contains evidence of the type and the underlying
-- untype expression. This is essentially the type of SQL
-- expressions. Constructing types of these expressions directly is unsafe.

data SQLValProto a b (x :: SQLType) where 
  SSQLAtom :: a -> SQLValProto a b 'SQLAtom 
  SSQLBool :: a -> SQLValProto a b 'SQLBool 
  SSQLRow :: b -> Prod SingT ts -> SQLValProto a b ('SQLRow ts)
  SSQLVec :: b -> Prod SingT ts -> SQLValProto a b ('SQLVec ts) 

bimapProto :: (a -> a') -> (b -> b') -> SQLValProto a b x -> SQLValProto a' b' x 
bimapProto f _ (SSQLAtom a) = SSQLAtom (f a) 
bimapProto f _ (SSQLBool a) = SSQLBool (f a) 
bimapProto _ g (SSQLRow b ts) = SSQLRow (g b) ts
bimapProto _ g (SSQLVec b ts) = SSQLVec (g b) ts


newtype SQLVal a = SQLVal { getSQLVal :: SQLValProto ValueExpr QueryExpr a }

-- Semantics in the interpreter 
data SQLValSem (x :: SQLRefType) where 
  Unit :: SQLValSem 'SQLUnit
  Method_ :: (Sing nm, Sing args, Sing out) => Name -> SQLValSem ('SQLMethod nm args out) 
  Ref_ :: Sing x => Name -> SQLValSem ('SQLRef x) 
  Val_ :: SQLVal x -> SQLValSem ('Ty x) 
  
type SQLValRef x = SQLValSem ('SQLRef x)
type SQLMethodRef nm args out = SQLValSem ('SQLMethod nm args out) 

unsafeSqlValFromName :: forall x . Sing x => Name -> SQLVal x 
unsafeSqlValFromName nm = SQLVal $ bimapProto nm0 nm1 (getSQLSing sing)
  where nm0 = const $ Iden [nm]
        nm1 = const $ Table [nm] 

deref :: forall x . SQLValRef x -> SQLVal x 
deref (Ref_ nm) = unsafeSqlValFromName nm 

-- Pattern match only (no constructor syntax). These can safely be exported and
-- constitute what can and cannot be distinguished at expression compile time. 
pattern Method nm <- Method_ nm 
pattern Ref x <- Ref_ x 
pattern Val x <- Val_ x 

instance DecideEq (SingT :: SQLType -> *) where 
  SQLSing (SSQLAtom ()) %== SQLSing (SSQLAtom ()) = Just Refl 
  SQLSing (SSQLRow () ts0) %== SQLSing (SSQLRow () ts1) = fmap (cong Refl) (ts0 %== ts1)
  SQLSing (SSQLVec () ts0) %== SQLSing (SSQLVec () ts1) = fmap (cong Refl) (ts0 %== ts1)
  _ %== _ = Nothing 

instance (DecideEq (SingT :: k0 -> *), DecideEq (SingT :: k1 -> *)) => DecideEq (SingT :: RecLabel k0 k1 -> *) where 
  SRecLabel a0 b0 %== SRecLabel a1 b1 = liftA2 (cong2 Refl) (a0 %== a1) (b0 %== b1) 

-- SQL statements

data TableSpec ts 
data ColumnSpec ts 
data SQLMethod nm ts out 

-- Used to distinguish sql methods from statements. The only difference 
-- is that a method cannot be "sequenced" with `:>>='. Essentially this
-- allows us to define 
data SQLSem = Stmt | Mthd 

type SQLStatement = SQLSt 'Stmt

data SQLSt (x :: SQLSem) (a :: SQLRefType) where
  Insert :: TableSpec ts -> SQLVal ('SQLRow ts) -> SQLStatement 'SQLUnit 
  -- Given a table and a query, insert those values into that table.

  Delete :: TableSpec ts -> SQLVal 'SQLBool -> SQLStatement 'SQLUnit 
  -- Delete from a table those values specified by the predicate
 
  Update :: TableSpec ts -> SQLVal 'SQLBool -> ColumnSpec ts -> SQLStatement 'SQLUnit 
  -- Same as above, this time taking two functions, the first is again the where
  -- clause, the 2nd computes the values to be updated. 

  SetRef :: SQLValRef x -> SQLVal x -> SQLStatement 'SQLUnit 
  -- Set the value of a reference to the given value. 

  NewRef :: SQLTypeS a -> Maybe String -> Maybe (SQLVal a) -> SQLStatement ('SQLRef a) 
  -- Creates a new reference of the given type. Optionally takes a name to use
  -- as a prototype for the new name, and an initial value. The default initial
  -- value of the reference is null.

  MakeTable :: TableSpec t -> SQLStatement 'SQLUnit 
  DropTable :: TableSpec t -> SQLStatement 'SQLUnit 
  -- Create/dropping tables 

  IfSQL :: SQLVal 'SQLBool -> SQLStatement a -> SQLStatement a -> SQLStatement 'SQLUnit  
  -- An If statement takes a boolean valued expression. 
 
  (:>>=) :: SQLStatement a -> (SQLValSem a -> SQLSt x b) -> SQLSt x b 
  SQLRet :: SQLVal a -> SQLSt x ('Ty a)
  -- Semantics. Only allowed for sql types. 

  SQLFunCall :: SQLMethodRef nm ts out -> Prod SQLVal ts -> SQLStatement ('Ty out) 
  SQLDefunMethod :: SQLMethod nm ts out -> SQLStatement ('SQLMethod nm ts out)
  -- Methods 

