{-# LANGUAGE PatternSynonyms, NoMonomorphismRestriction, OverloadedStrings, LambdaCase, EmptyCase #-} 
{-# LANGUAGE TemplateHaskell, QuasiQuotes, ScopedTypeVariables, PolyKinds, UndecidableInstances, DataKinds, DefaultSignatures #-}
{-# LANGUAGE PartialTypeSignatures, TypeOperators #-} 
{-# OPTIONS -fno-warn-unticked-promoted-constructors #-} 

-- Various utilities used by ECA2SQL 

module Database.Design.Ampersand.ECA2SQL.Utils 
  ( module Database.Design.Ampersand.ECA2SQL.Utils 
  , module GHC.TypeLits 
  , module Data.Proxy
  , module GHC.Exts
  , module Data.Type.Equality
  ) where 

import Control.Applicative 
import Unsafe.Coerce 
import Data.Proxy (Proxy(..), KProxy(..))
import GHC.TypeLits (Symbol, symbolVal, sameSymbol, KnownSymbol)
import qualified GHC.TypeLits as TL  
import GHC.Exts (Constraint)
import Data.Type.Equality ((:~:)(..))
import GHC.Exts (IsString(..))
import Language.SQL.SimpleSQL.Syntax (Name(..))

instance IsString Name where fromString = Name 


-- Given a functor `f', `Prod f' constructs the n-ary product category of `f'
data Prod (f :: k -> *) (xs :: [k]) where 
  PNil :: Prod f '[] 
  PCons :: f x -> Prod f xs -> Prod f (x ': xs) 

infixr 5 :> 
pattern x :> xs = PCons x xs 

someProd :: [Exists f] -> Exists (Prod f)
someProd [] = Ex PNil 
someProd (Ex x:xs) = someProd xs #>> Ex . PCons x

data Sum (f :: k -> *) (xs :: [k]) where 
  SHere :: f x -> Sum f (x ': xs) 
  SThere :: Sum f xs -> Sum f (x ': xs) 

-- The constraint `All c xs' holds exactly when `c x' holds for all `x' in `xs'
class All (c :: k -> Constraint) (xs :: [k]) where   
  mkProdC :: Proxy c -> (forall a . c a => p a) -> Prod p xs 

instance All (c :: k -> Constraint) '[] where mkProdC _ _ = PNil 
instance (All c xs, c x) => All c (x ': xs) where mkProdC pr k = PCons k (mkProdC pr k) 

-- non emtpy list predicate
type family NonEmpty (xs :: [k]) :: Constraint where 
  NonEmpty (x ': xs) = () 

-- Reify a class as a value
data Dict p where Dict :: p => Dict p 

-- Existence proof 
data Exists p where Ex :: p x -> Exists p

infixr 3 #>>
(#>>) :: Exists p -> (forall x . p x -> r) -> r
(#>>) (Ex x) f = f x

-- Manipulating equality proofs 
cong :: f :~: g -> a :~: b -> f a :~: g b 
cong Refl Refl = Refl 

cong2 :: f :~: g -> a :~: a' -> b :~: b' -> f a b :~: g a' b' 
cong2 Refl Refl Refl = Refl 

cong3 :: f :~: g -> a :~: a' -> b :~: b' -> c :~: c' -> f a b c :~: g a' b' c' 
cong3 Refl Refl Refl Refl = Refl 

-- `x' is an element of `xs' if there exists a `y' in `xs' such that it is equal
-- to `x'
newtype Elem (x :: k) (xs :: [k]) = MkElem { getElem :: Sum ((:~:) x) xs }

type family IsElem (x :: k) (xs :: [k]) :: Constraint where 
  IsElem x (x ': xs) = () 
  IsElem x (y ': xs) = IsElem x xs 

-- Also known as flip 
data AppliedTo (x :: k) (f :: k -> *) where Ap :: f x -> x `AppliedTo` f 

data Flip (f :: k0 -> k1 -> *) (x :: k1) (y :: k0) where 
  Flp :: f y x -> Flip f x y

newtype (:.:) (f :: k1 -> *) (g :: k0 -> k1) x = Cmp { unCmp :: f (g x) }
data (:*:) (f :: k0 -> *) (g :: k0 -> *) (x :: k0) = (:*:) (f x) (g x)
newtype K a (x :: k) = K { unK :: a } 
newtype Id a = Id { unId :: a } 

-- Type level OR 
type family (&&) (x :: Bool) (y :: Bool) :: Bool where 
  'False && x = 'False 
  x && 'False = 'False 
  'True && 'True = 'True 

(|&&) :: SingT a -> SingT b -> SingT (a && b)
SFalse |&& _ = SFalse 
_ |&& SFalse = SFalse 
STrue |&& STrue = STrue 

-- Decidable equality 
class DecideEq (f :: k -> *) where 
  (%==) :: forall x y . f x -> f y -> Maybe (x :~: y) 

-- truly decidable equality. Unfortunatley, it is rarely practical.. 
data DecEq (x :: k) (y :: k) where 
  DecYes :: DecEq a a 
  DecNo  :: (forall r . a :~: b -> r) -> DecEq a b 

mapDec :: ((x ~ y) => x' :~: y') -> (forall q. (x' ~ y') => (forall r . x :~: y -> r) -> q) -> DecEq x y -> DecEq x' y' 
mapDec yes _ DecYes = case yes of { Refl -> DecYes } 
mapDec _ no (DecNo p) = DecNo (\case { Refl -> no p })

natEq :: NatSing a -> NatSing b -> DecEq a b 
natEq SZ SZ = DecYes 
natEq SZ{} SS{} = DecNo $ \case 
natEq SS{} SZ{} = DecNo $ \case 
natEq (SS n) (SS m) = mapDec Refl (\p -> p Refl) $ natEq n m 

eqList :: (forall (x :: k) (y :: k) . SingT x -> SingT y -> DecEq x y) 
       -> SingT (xs :: [k]) -> SingT (ys :: [k]) -> DecEq xs ys 
eqList _ SNil SNil = DecYes 
eqList f (SCons x xs) (SCons y ys) = 
  case f x y of 
    DecYes -> mapDec Refl (\p -> p Refl) $ eqList f xs ys 
    DecNo p -> DecNo $ \case { Refl -> p Refl } 
eqList _ SCons{} SNil{} = DecNo $ \case 
eqList _ SNil{} SCons{} = DecNo $ \case 

instance (DecideEq f) => DecideEq (Prod f) where 
  PNil %== PNil = Just Refl 
  PCons x xs %== PCons y ys = liftA2 (cong2 Refl) (x %== y) (xs %== ys) 
  _ %== _ = Nothing 

instance DecideEq (SingT :: Nat -> *) where 
  SZ %== SZ = Just Refl 
  SS n %== SS m = fmap (cong Refl) $ n %== m 
  _ %== _ = Nothing 

instance DecideEq (SingT :: Symbol -> *) where 
  SSymbol s0 %== SSymbol s1 = sameSymbol s0 s1 

-- Generic singleton indexed on kind
data family SingT (y :: k) 

class Sing x where 
  sing :: SingT x 

class ValueSing (kp :: KProxy k) where 
  type ValOfSing (kp :: KProxy k)
  sing2val :: forall (x :: k) . SingT x -> ValOfSing kp 
  val2sing :: Proxy kp -> ValOfSing kp -> Exists (SingT :: k -> *)

-- Based on http://okmij.org/ftp/Haskell/tr-15-04.pdf and
-- https://hackage.haskell.org/package/reflection-2.1.1.1/docs/src/Data-Reflection.html#reify

newtype Magic x r = Magic (Sing x => Proxy x -> r)

withSingT :: forall (x :: k) r . SingT x -> (Sing x => Proxy x -> r) -> r
withSingT a k = unsafeCoerce (Magic k :: Magic x r) a Proxy   
{-# INLINE withSingT #-}

-- Symbol
data instance SingT (y :: Symbol) where 
  SSymbol :: KnownSymbol x => !(Proxy x) -> SingT x 
type SymbolSing = (SingT :: Symbol -> *)
instance KnownSymbol x => Sing x where 
  sing = SSymbol Proxy 

instance ValueSing ('KProxy :: KProxy Symbol) where 
  type ValOfSing ('KProxy :: KProxy Symbol) = String  
  sing2val (SSymbol x) = TL.symbolVal x 
  val2sing _ str = case TL.someSymbolVal str of { TL.SomeSymbol x -> Ex (SSymbol x) } 

symbolKindProxy = Proxy :: Proxy ('KProxy :: KProxy Symbol)

data CompareSymbol a b where 
  SymbolLT :: !(TL.CmpSymbol a b :~: 'LT) -> CompareSymbol a b 
  SymbolEQ :: !(TL.CmpSymbol a b :~: 'EQ) -> CompareSymbol a b 
  SymbolGT :: !(TL.CmpSymbol a b :~: 'GT) -> CompareSymbol a b 

compareSymbol' :: SingT x -> SingT y -> CompareSymbol x y
compareSymbol' (SSymbol x) (SSymbol y) = compareSymbol x y  

compareSymbol :: forall x y . (TL.KnownSymbol x, TL.KnownSymbol y) => Proxy x -> Proxy y -> CompareSymbol x y 
compareSymbol x y =  
  let trustMe :: forall a b . a :~: b 
      trustMe = unsafeCoerce (Refl :: () :~: ())
  in case compare (TL.symbolVal x) (TL.symbolVal y) of 
       LT -> SymbolLT (trustMe :: TL.CmpSymbol x y :~: 'LT) 
       EQ -> SymbolEQ (trustMe :: TL.CmpSymbol x y :~: 'EQ) 
       GT -> SymbolGT (trustMe :: TL.CmpSymbol x y :~: 'GT) 

-- Nat 
data instance SingT (y :: Nat) where 
  SZ :: SingT 'Z 
  SS :: !(SingT n) -> SingT ('S n) 
type NatSing = (SingT :: Nat -> *)
instance Sing 'Z where sing = SZ 
instance Sing n => Sing ('S n) where sing = SS sing 

data Nat = Z | S Nat 

natVal :: forall x . Sing x => Proxy (x :: Nat) -> Integer 
natVal _ = go (sing :: SingT x) where 
  go :: SingT (a :: Nat) -> Integer 
  go SZ = 0 
  go (SS n) = 1 + go n 

-- eqNat :: SingT (n :: Nat) -> SingT m -> SingT (n == m) 
-- eqNat SZ SZ = STrue 
-- eqNat (SS n) (SS m) = 
--   case eqNat n m of 
--     STrue -> _ 
    -- SFalse -> SFalse 

-- Inductive type literals 

data IsoNat n m where 
  IsoZ :: IsoNat 0 'Z 
  IsoS :: !(SingT n) -> IsoNat (n TL.+ 1) ('S n') 

type family FromTL (n :: TL.Nat) :: Nat where 
  FromTL 0 = 'Z 
  FromTL n = 'S (FromTL (n TL.- 1))

type family ToTL (n :: Nat) :: TL.Nat where 
  ToTL 'Z = 0 
  ToTL (S n) = ToTL n TL.+ 1 

data instance SingT (y :: TL.Nat) where 
  NatSingI :: (TL.KnownNat n) => !(Proxy n) -> SingT n 

-- BOOl
data instance SingT (x :: Bool) where 
  STrue :: SingT 'True 
  SFalse :: SingT 'False 
type BoolSing = (SingT :: Bool -> *) 
instance Sing 'True where sing = STrue 
instance Sing 'False where sing = SFalse 


-- Maybe 
data instance SingT (x :: Maybe k) where 
  SNothing :: SingT 'Nothing 
  SJust :: !(SingT x) -> SingT ('Just x)
type MaybeSing = (SingT :: Maybe k -> *) 
instance Sing 'Nothing where sing = SNothing 
instance Sing x => Sing ('Just x) where sing = SJust sing  

-- Record lable kind

data RecLabel a b = a ::: b

data instance SingT (x :: RecLabel a b) where 
  SRecLabel :: !(SingT a) -> !(SingT b) -> SingT (a ::: b)

instance (Sing a, Sing b) => Sing (a ::: b) where sing = SRecLabel sing sing  

type family RecAssocs (xs :: [RecLabel a b]) :: [b] where 
  RecAssocs '[] = '[] 
  RecAssocs ((nm ::: ty) ': xs) = ty ': RecAssocs xs

type family RecLabels (xs :: [RecLabel a b]) :: [a] where 
  RecLabels '[] = '[] 
  RecLabels ((nm ::: ty) ': xs) = nm ': RecLabels xs

type family CaseOrdering (x :: Ordering) (a :: k) (b :: k) (c :: k) :: k where 
  CaseOrdering 'LT a b c = a 
  CaseOrdering 'EQ a b c = b 
  CaseOrdering 'GT a b c = c 

-- Lookup a value in a list of rec labels 
type family LookupRec (xs :: [RecLabel Symbol k]) (x :: Symbol) :: k where 
  LookupRec ( (nm ::: ty) ': rest ) nm' = CaseOrdering (TL.CmpSymbol nm nm') (LookupRec rest nm') ty (LookupRec rest nm') 

type family LookupIx (xs :: [k]) (i :: TL.Nat) :: k where 
  LookupIx ( x ': xs ) 0 = x 
  LookupIx ( x ': xs ) n = LookupIx xs (n TL.- 1)

lookupRec :: forall (xs :: [RecLabel Symbol b]) (nm :: Symbol) (r :: b) . (LookupRec xs nm ~ r) => Prod SingT xs -> SingT nm -> SingT r 
lookupRec PNil x = x `seq` error "lookupSing: impossible" 
lookupRec (PCons (SRecLabel nm ty) rest) nm' = 
  case compareSymbol' nm nm' of 
    SymbolEQ Refl -> ty 
    SymbolLT Refl -> lookupRec rest nm' 
    SymbolGT Refl -> lookupRec rest nm' 

        
-- List
prod2sing :: Prod SingT xs -> SingT xs 
prod2sing PNil = SNil 
prod2sing (PCons x xs) = SCons x (prod2sing xs)

sing2prod :: SingT xs -> Prod SingT xs 
sing2prod SNil = PNil 
sing2prod (SCons x xs) = x :> sing2prod xs 

data instance SingT (x :: [k]) where 
  SNil :: SingT '[] 
  SCons :: !(SingT x) -> !(SingT xs) -> SingT (x ': xs) 
type ListSing = (SingT :: [k] -> *) 
instance All Sing xs => Sing xs where sing = prod2sing $ mkProdC (Proxy :: Proxy Sing) sing 

instance (DecideEq (SingT :: k -> *)) => DecideEq (SingT :: [k] -> *) where 
  SNil %== SNil = Just Refl 
  SCons x xs %== SCons y ys = liftA2 (cong2 Refl) (x %== y) (xs %== ys) 
  _ %== _ = Nothing 

-- Type level if. Note that this is STRICT 
type family If (a :: Bool) (x :: k)(y :: k) :: k where 
  If 'True x y = x 
  If 'False x y = y 

-- If forms an applicative of sorts  
newtype IfA (c :: Bool) (x :: *) (y :: *) = IfA { getIfA :: If c x y } 

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


-- uncurry

class Uncurry f args o r | f args o -> r where 
  uncurryN :: (Prod f args -> f o) -> r

instance (f o ~ r) => Uncurry f '[] o r where 
  uncurryN f = f PNil 

instance (Uncurry f args o r, q ~ (f arg -> r)) => Uncurry f (arg ': args) o q where 
  uncurryN f arg = uncurryN (f . PCons arg) 
