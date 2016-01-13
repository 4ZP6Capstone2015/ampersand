{-# LANGUAGE PatternSynonyms, NoMonomorphismRestriction, OverloadedStrings, LambdaCase, EmptyCase #-} 
{-# LANGUAGE TemplateHaskell, QuasiQuotes, ScopedTypeVariables, PolyKinds, UndecidableInstances, DataKinds, DefaultSignatures #-}
{-# LANGUAGE PartialTypeSignatures #-} 
{-# OPTIONS -fno-warn-unticked-promoted-constructors #-} 

module Database.Design.Ampersand.ECA2SQL.TypedSQL 
  ( Prod(..), Sum(..), All(..), Elem(..), AppliedTo(..), DecideEq(..), Sing(..), SingT(..), (:~:)(..), withSingT
  , IfA(..), if_ap, if_pure
  -- SQL stuff
  , Symbol, SymbolSing, Nat, NatSing, RecLabel(..), SQLType(..), SQLRefType, SQLRow, SQLVec, SQLRel, SQLAtom, SQLBool
  , SQLTypeS, SQLValProto, bimapProto, foldProto, SQLVal, SQLValSem(Unit) -- Ctrs not exported!
  , pattern Method, pattern Ref, pattern Val
  , unsafeSqlValFromName, deref
  , TableSpec, SQLMethod(..), SQLSem, SQLStatement, IsScalarType, isScalarType
  , SQLSt(..)
  , getSQLVal, elimSQLVal, unsafeSQLVal, typeOf 
  , module Sm
  ) where 

import Control.Applicative
import qualified Language.SQL.SimpleSQL.Syntax as Sm 
import Language.SQL.SimpleSQL.Syntax (ValueExpr(..), QueryExpr(..), TableRef(..), Name(..))  
import Data.Proxy (Proxy(..), KProxy(..))
import qualified GHC.TypeLits as TL 
import GHC.TypeLits (Symbol)
import GHC.Exts (Constraint)
import Data.Type.Equality ((:~:)(..))
import Unsafe.Coerce 

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

cong2 :: f :~: g -> a :~: a' -> b :~: b' -> f a b :~: g a' b' 
cong2 Refl Refl Refl = Refl 

-- cong3 :: f :~: g -> a :~: a' -> b :~: b' -> c :~: c' -> f a b c :~: g a' b' c' 
-- cong3 Refl Refl Refl Refl = Refl 

newtype Elem (x :: k) (xs :: [k]) = MkElem { getElem :: Sum ((:~:) x) xs }

data AppliedTo (x :: k) (f :: k -> *) where Ap :: f x -> x `AppliedTo` f 

type family (&&) (x :: Bool) (y :: Bool) :: Bool where 
  'False && x = 'False 
  x && 'False = 'False 
  'True && 'True = 'True 

(.&&) :: SingT a -> SingT b -> SingT (a && b)
SFalse .&& _ = SFalse 
_ .&& SFalse = SFalse 
STrue .&& STrue = STrue 

-- Decidable equality 
class DecideEq (f :: k -> *) where 
  (%==) :: forall x y . f x -> f y -> Maybe (x :~: y) 

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

-- Based on http://okmij.org/ftp/Haskell/tr-15-04.pdf and
-- https://hackage.haskell.org/package/reflection-2.1.1.1/docs/src/Data-Reflection.html#reify

newtype Magic x r = Magic (Sing x => r)

withSingT :: forall (x :: k) r . SingT x -> (Sing x => r) -> r 
withSingT a k = unsafeCoerce (Magic k :: Magic x r) a   
{-# INLINE withSingT #-}

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

-- BOOl
data instance SingT (x :: Bool) where 
  STrue :: SingT 'True 
  SFalse :: SingT 'False 

-- SQL Types 

data RecLabel a b = a ::: b
data SQLType 
  = SQLAtom                            -- All scalar types. Should be split into the different types it represents 
  | SQLBool                            -- A boolean
  | SQLRel SQLType                     -- Type of relations over some underlying type
  | SQLRow [RecLabel Symbol SQLType]   -- A row in a table. 
  | SQLVec [SQLType]                   -- Essentially an unnamed row. 

-- SQL types along with types in domain of interpretation 
data SQLRefType 
  = Ty SQLType 
  | SQLRef SQLType 
  | SQLUnit 
  | SQLMethod [SQLType] SQLType 

-- Useful type synonyms 
type SQLRow xs = 'Ty ('SQLRow xs) 
type SQLVec xs = 'Ty ('SQLVec xs) 
type SQLRel x = 'Ty ('SQLRel x) 
type SQLAtom = 'Ty 'SQLAtom 
type SQLBool = 'Ty 'SQLBool 

-- Singleton for record labels
data instance SingT (x :: RecLabel a b) where 
  SRecLabel :: SingT a -> SingT b -> SingT (a ::: b) 

-- Singletong for SQL values. It is the same as SQL values by construction. 
type SQLTypeS = (SingT :: SQLType -> *) 
newtype instance SingT (x :: SQLType) = SQLSing { getSQLSing :: SQLValProto () () x }

-- Determine if a SQL type is a really a scalar type. 
type family IsScalarType (x :: k) :: Bool where 
  IsScalarType ('SQLRel x) = 'False 
  IsScalarType ('SQLRow x) = IsScalarType x 
  IsScalarType ('SQLVec x) = IsScalarType x 
  IsScalarType ((nm :: Symbol) ::: (x :: SQLType)) = IsScalarType x 
  IsScalarType '[] = 'True 
  IsScalarType (x ': xs) = IsScalarType x && IsScalarType xs 
  IsScalarType (x :: SQLType) = 'True

isScalarType :: SingT (x :: SQLType) -> SingT (IsScalarType x)
isScalarType (SQLSing (SSQLAtom ())) = STrue 
isScalarType (SQLSing (SSQLBool ())) = STrue 
isScalarType (SQLSing (SSQLVec () vs0)) = 
  case vs0 of 
    PNil -> STrue
    PCons v vs ->  isScalarType v .&& isScalarType (SQLSing $ SSQLVec () vs)
isScalarType (SQLSing (SSQLRow () ts0)) = 
  case ts0 of 
    PNil -> STrue 
    PCons (SRecLabel _ t) ts -> isScalarType t .&& isScalarType (SQLSing $ SSQLRow () ts)
isScalarType (SQLSing (SSQLRel () _)) = SFalse   

-- Singletons for SQLType 
instance (Sing a, Sing b) => Sing (a ::: b) where sing = SRecLabel sing sing 
instance (All Sing xs) => Sing ('SQLRow xs) where sing = SQLSing $ SSQLRow () (mkProdC (Proxy :: Proxy Sing) sing) 
instance (All Sing xs) => Sing ('SQLVec xs) where sing = SQLSing $ SSQLVec () (mkProdC (Proxy :: Proxy Sing) sing) 
instance Sing 'SQLAtom where sing = SQLSing $ SSQLAtom ()

-- A reference to a SQL value. Contains evidence of the type and the underlying
-- untype expression. This is essentially the type of SQL
-- expressions. Constructing types of these expressions directly is unsafe.
data SQLValProto scalar vector (x :: SQLType) where 
  SSQLAtom :: a -> SQLValProto a b 'SQLAtom 
  SSQLBool :: a -> SQLValProto a b 'SQLBool
  SSQLRow :: a -> Prod SingT ts -> SQLValProto a b ('SQLRow ts)
  SSQLVec :: a -> Prod SingT ts -> SQLValProto a b ('SQLVec ts) 
  SSQLRel :: v -> SingT x -> SQLValProto s v ('SQLRel x) 

bimapProto :: (a -> a') -> (b -> b') -> SQLValProto a b x -> SQLValProto a' b' x 
bimapProto f _ (SSQLAtom a) = SSQLAtom (f a) 
bimapProto f _ (SSQLBool a) = SSQLBool (f a) 
bimapProto _ g (SSQLRel x t) = SSQLRel (g x) t 
bimapProto f _ (SSQLRow b ts) = SSQLRow (f b) ts
bimapProto f _ (SSQLVec b ts) = SSQLVec (f b) ts

foldProto :: (a -> r) -> (b -> r) -> SQLValProto a b x -> r
foldProto f _ (SSQLAtom a) = f a 
foldProto f _ (SSQLBool a) = f a 
foldProto _ g (SSQLRel x _) = g x 
foldProto f _ (SSQLRow b _) = f b
foldProto f _ (SSQLVec b _) = f b

-- A SQL value contains value expressions 
newtype SQLVal a = SQLVal (SQLValProto ValueExpr QueryExpr a)

-- Get the type of a value 
typeOf :: SQLVal a -> SingT a 
typeOf (SQLVal x) = SQLSing (bimapProto (const ()) (const ()) x) 

-- Get the actual tree
getSQLVal :: SQLVal x -> SQLValProto ValueExpr QueryExpr x
getSQLVal (SQLVal x) = x 

{-
-- Lift an unary function to a sql value
unsafeSQLOp1 :: forall x . If (IsScalarType x) (ValueExpr -> ValueExpr) (QueryExpr -> QueryExpr) 
             -> SQLVal x -> SQLVal x 
unsafeSQLOp1 f x = 
  let fun = IfA f :: IfA (IsScalarType x) (ValueExpr -> ValueExpr) (QueryExpr -> QueryExpr)
      ty_x = typeOf x 
  in withSingT ty_x $ 
     withSingT (isScalarType ty_x) $ 
     unsafeSQLVal $ getIfA $ if_ap fun (IfA $ elimSQLVal x) 

unsafeSQLOp2 :: forall x . If (IsScalarType x) (ValueExpr -> ValueExpr -> ValueExpr) (QueryExpr -> QueryExpr -> QueryExpr) 
             -> SQLVal x -> SQLVal x -> SQLVal x 
unsafeSQLOp2 f x y = 
  let fun = IfA f :: IfA (IsScalarType x) (ValueExpr -> ValueExpr -> ValueExpr) (QueryExpr -> QueryExpr -> QueryExpr) 
      ty_x = typeOf x 
  in withSingT ty_x $ 
     withSingT (isScalarType ty_x) $  
     unsafeSQLVal $ getIfA $ fun `if_ap` (IfA $ elimSQLVal x) `if_ap` (IfA $ elimSQLVal y)
 -}

-- Eliminate a sqlVal with proof of the resulting type. 
elimSQLVal :: forall x . SQLVal x -> If (IsScalarType x) ValueExpr QueryExpr  
elimSQLVal (SQLVal x) = 
  case isScalarType (SQLSing $ bimapProto (const ()) (const ()) x) of 
    STrue  -> foldProto id (\_ -> error "elimSQLVal:impossible") x 
    SFalse -> foldProto (Values . pure . pure {- TODO: Is this safe? -} ) id x 

-- Lift a primitive value to a sql value 
unsafeSQLVal :: forall x . Sing x => If (IsScalarType x) ValueExpr QueryExpr -> SQLVal x
unsafeSQLVal val = let s = sing :: SingT x in 
  case isScalarType s of 
    STrue -> SQLVal $ bimapProto (const val) (const $ error "unsafeSQLVal:impossible") $ getSQLSing s
    SFalse -> SQLVal $ bimapProto (const $ error "unsafeSQLVal:impossible") (const val) $ getSQLSing s

type family If (a :: Bool) (x :: k)(y :: k) :: k where 
  If 'True x y = x 
  If 'False x y = y 

newtype IfA (c :: Bool) (x :: *) (y :: *) = IfA { getIfA :: If c x y } 


-- If forms an applicative of sorts 

if_pure :: forall a b cond . Sing cond => a -> b -> IfA cond a b 
if_pure a b = IfA $ 
  case sing :: SingT cond of 
    STrue -> a 
    SFalse -> b 

if_ap :: forall a b a' b' cond. Sing cond => IfA cond (a -> a') (b -> b') -> IfA cond a b -> IfA cond a' b' 
if_ap (IfA f) (IfA a) = IfA $ 
  case sing :: SingT cond of 
    STrue -> f a 
    SFalse -> f a 

-- Semantics in the interpreter 
data SQLValSem (x :: SQLRefType) where 
  Unit :: SQLValSem 'SQLUnit
  Method_ :: (Sing args, Sing out) => Name -> SQLValSem ('SQLMethod args out) 
  Ref_ :: Sing x => Name -> SQLValSem ('SQLRef x) 
  Val_ :: SQLVal x -> SQLValSem ('Ty x) 
  
-- A SQLValRef is a reference to a sql value in the domain of the semantic interpretation. 
type SQLValRef x = SQLValSem ('SQLRef x)

-- Same as above, but a reference to a method is distinct from that to a value. 
type SQLMethodRef args out = SQLValSem ('SQLMethod args out) 

unsafeSqlValFromName :: forall x . Sing x => Name -> SQLVal x 
unsafeSqlValFromName nm = SQLVal $ bimapProto nm0 nm1 (getSQLSing sing)
  where nm0 = const $ Iden [nm]
        nm1 = const $ Table [nm] 

deref :: forall x . SQLValRef x -> SQLVal x 
deref (Ref_ nm) = unsafeSqlValFromName nm 

-- Pattern match only (no constructor syntax). These permit access (but not the
-- ability to construct) to the underlying untyped representation. 
pattern Method nm <- Method_ nm 
pattern Ref x <- Ref_ x 
pattern Val x <- Val_ x 

instance DecideEq (SingT :: SQLType -> *) where 
  SQLSing (SSQLAtom ()) %== SQLSing (SSQLAtom ()) = Just Refl 
  SQLSing (SSQLBool ()) %== SQLSing (SSQLBool ()) = Just Refl 
  SQLSing (SSQLRel () x) %== SQLSing (SSQLRel () y) = fmap (cong Refl) (x %== y)
  SQLSing (SSQLRow () ts0) %== SQLSing (SSQLRow () ts1) = fmap (cong Refl) (ts0 %== ts1)
  SQLSing (SSQLVec () ts0) %== SQLSing (SSQLVec () ts1) = fmap (cong Refl) (ts0 %== ts1)
  _ %== _ = Nothing 

instance (DecideEq (SingT :: k0 -> *), DecideEq (SingT :: k1 -> *)) => DecideEq (SingT :: RecLabel k0 k1 -> *) where 
  SRecLabel a0 b0 %== SRecLabel a1 b1 = liftA2 (cong2 Refl) (a0 %== a1) (b0 %== b1) 

-- SQL statements

-- The specification of a table is a reference to a relation on rows 
-- of the table type. 
type TableSpec t = SQLValRef ('SQLRel ('SQLRow t))

{-
type family RecsAssocs (ts :: [RecLabel a b]) :: [b] where 
  RecsAssocs '[] = '[] 
  RecsAssocs ((x ::: t) ': r) = t ': RecsAssocs r 

data ColumnSpec (ts :: [RecLabel Symbol SQLType]) where 
  RowExpr :: SQLVal ('SQLRel ('SQLRow ts)) -> ColumnSpec ts 
  -- a row expression corresonding exactly to the given table

  VecExpr :: (RecsAssocs ts ~ vs) => SQLVal ('SQLRel ('SQLVec vs)) -> ColumnSpec ts 
  -- a vector expression which can be cast to that table type

  ScalarExpr :: Sing nm => SQLVal ('SQLRel t) -> ColumnSpec '[ nm ::: t ]
  -- In the case that the table has one row, a relational expression containing exactly that type. 
-}

data SQLMethod ts out where 
  MkSQLMethod :: Maybe String -> (Prod SQLVal ts -> SQLSt 'Mthd ('Ty out)) -> SQLMethod ts out 

-- Used to distinguish sql methods from statements. The only difference 
-- is that a method cannot be "sequenced" with `:>>='. Essentially this
-- allows us to define 
data SQLSem = Stmt | Mthd 

type SQLStatement = SQLSt 'Stmt

data SQLSt (x :: SQLSem) (a :: SQLRefType) where
  Insert :: TableSpec ts -> SQLVal ('SQLRel ('SQLRow ts)) -> SQLStatement 'SQLUnit 
  -- Given a table and a query, insert those values into that table. Overloaded to work with both vectors and 
  -- tables. If the input is a table, it is implicitly casted to the shape of the table before insertion. 

  Delete :: TableSpec ts -> SQLVal 'SQLBool -> SQLStatement 'SQLUnit 
  -- Delete from a table those values specified by the predicate
 
  Update :: TableSpec ts -> SQLVal 'SQLBool -> SQLVal ('SQLRow ts) -> SQLStatement 'SQLUnit 
  -- Same as above, this time taking two functions, the first is again the where
  -- clause, the 2nd computes the values to be updated. 

  SetRef :: SQLValRef x -> SQLVal x -> SQLStatement 'SQLUnit 
  -- Set the value of a reference to the given value. 

  NewRef :: (IsScalarType a ~ 'True) => SQLTypeS a -> Maybe String -> Maybe (SQLVal a) -> SQLStatement ('SQLRef a) 
  -- Creates a new reference of the given type. Optionally takes a name to use
  -- as a prototype for the new name, and an initial value. The default initial
  -- value of the reference is null. We only allow references to scalar types -
  -- otherwise, a table should be used.

  MakeTable :: TableSpec t -> SQLStatement ('SQLRef ('SQLRel ('SQLRow t)))
  -- Returns a reference to a relation on values of records of the table spec. 

  DropTable :: TableSpec t -> SQLStatement 'SQLUnit 
  -- Create/dropping tables. Should really bind some sort of table reference, 
  -- but this prevents referencing tables which are known to exist, but
  -- are never bound in the tree. Perhaps there should be some sort of 
  -- "assumptions" constructor for tables?

  IfSQL :: SQLVal 'SQLBool -> SQLSt t0 a -> SQLSt t1 a -> SQLStatement a   
  -- An If statement takes a boolean valued expression. 
 
  (:>>=) :: SQLStatement a -> (SQLValSem a -> SQLSt x b) -> SQLSt x b 
  SQLNoop :: SQLStatement 'SQLUnit 
  SQLRet :: SQLVal a -> SQLSt 'Mthd ('Ty a)
  -- Semantics. Only allowed for sql types. 

  SQLFunCall :: SQLMethodRef ts out -> Prod SQLVal ts -> SQLStatement ('Ty out) 
  SQLDefunMethod :: SQLMethod ts out -> SQLStatement ('SQLMethod ts out)
  -- Methods 

