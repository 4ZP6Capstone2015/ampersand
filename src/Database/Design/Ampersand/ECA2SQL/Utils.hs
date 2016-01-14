{-# LANGUAGE PatternSynonyms, NoMonomorphismRestriction, OverloadedStrings, LambdaCase, EmptyCase #-} 
{-# LANGUAGE TemplateHaskell, QuasiQuotes, ScopedTypeVariables, PolyKinds, UndecidableInstances, DataKinds, DefaultSignatures #-}
{-# LANGUAGE PartialTypeSignatures #-} 
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
import GHC.Exts (Constraint)
import Data.Type.Equality ((:~:)(..))
import GHC.Exts (IsString(..))
import Language.SQL.SimpleSQL.Syntax (Name(..))

instance IsString Name where fromString = Name 

-- Given a functor `f', `Prod f' constructs the n-ary product category of `f'
data Prod (f :: k -> *) (xs :: [k]) where 
  PNil :: Prod f '[] 
  PCons :: f x -> Prod f xs -> Prod f (x ': xs) 

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

-- Also known as flip 
data AppliedTo (x :: k) (f :: k -> *) where Ap :: f x -> x `AppliedTo` f 

data Flip (f :: k0 -> k1 -> *) (x :: k1) (y :: k0) where 
  Flp :: f y x -> Flip f x y

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

-- Based on http://okmij.org/ftp/Haskell/tr-15-04.pdf and
-- https://hackage.haskell.org/package/reflection-2.1.1.1/docs/src/Data-Reflection.html#reify

newtype Magic x r = Magic (Sing x => r)

withSingT :: forall (x :: k) r . SingT x -> (Sing x => r) -> r 
withSingT a k = unsafeCoerce (Magic k :: Magic x r) a   
{-# INLINE withSingT #-}

-- Symbol
data instance SingT (y :: Symbol) where 
  SSymbol :: KnownSymbol x => Proxy x -> SingT x 
type SymbolSing = (SingT :: Symbol -> *)
instance KnownSymbol x => Sing x where 
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
type BoolSing = (SingT :: Bool -> *) 
instance Sing 'True where sing = STrue 
instance Sing 'False where sing = SFalse 


-- Maybe 
data instance SingT (x :: Maybe k) where 
  SNothing :: SingT 'Nothing 
  SJust :: SingT x -> SingT ('Just x)
type MaybeSing = (SingT :: Maybe k -> *) 
instance Sing 'Nothing where sing = SNothing 
instance Sing x => Sing ('Just x) where sing = SJust sing  

-- Record lable kind

data RecLabel a b = a ::: b

data instance SingT (x :: RecLabel a b) where 
  SRecLabel :: SingT a -> SingT b -> SingT (a ::: b)

instance (Sing a, Sing b) => Sing (a ::: b) where sing = SRecLabel sing sing  

type family RecAssocs (xs :: [RecLabel a b]) :: [b] where 
  RecAssocs '[] = '[] 
  RecAssocs ((nm ::: ty) ': xs) = ty ': RecAssocs xs

type family RecLabels (xs :: [RecLabel a b]) :: [a] where 
  RecLabels '[] = '[] 
  RecLabels ((nm ::: ty) ': xs) = nm ': RecLabels xs

-- Lookup a value in a list of rec labels 
type family Lookup (xs :: [RecLabel a b]) (x :: a) :: b where 
  Lookup ( (nm ::: ty) ': rest ) nm = ty 
  Lookup ( (nm ::: ty) ': rest ) nm' = Lookup rest nm' 

{-
lookupSing :: (DecideEq (SingT :: a -> *), Lookup xs nm ~ r) => Prod SingT xs -> SingT (nm :: a) -> SingT r 
lookupSing PNil _ = error "lookupSing: impossible" 
lookupSing (PCons (SRecLabel nm ty) rest) nm' = 
  case nm %== nm' of 
    Just Refl -> ty 
    -- No clue how to write this properly.. the compiler can't tell that 
    --   nm /= nm'   =>   Lookup ( (nm ::: ty) : rest ) nm' == Lookup rest nm 
    -- because it doesn't know about the type inequality at all... 
    Nothing -> unsafeCoerce $ lookupSing rest nm' 
-}
        
-- List
newtype instance SingT (x :: [k]) = MkSList { getSList :: Prod SingT x } 
type ListSing = (SingT :: [k] -> *) 
instance All Sing xs => Sing xs where sing = MkSList $ mkProdC (Proxy :: Proxy Sing) sing 

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

