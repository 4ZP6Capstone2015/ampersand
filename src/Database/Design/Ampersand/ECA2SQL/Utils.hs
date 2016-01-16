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
  , module Database.Design.Ampersand.ECA2SQL.Equality 
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
import Database.Design.Ampersand.ECA2SQL.Equality 
import Database.Design.Ampersand.ECA2SQL.Singletons

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

{-
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
-}

-- Symbol 
symbolKindProxy = Proxy :: Proxy ('KProxy :: KProxy Symbol)

compareSymbol' :: SingT x -> SingT y -> SingT (TL.CmpSymbol x y)
compareSymbol' (SSymbol x) (SSymbol y) = compareSymbol x y  

compareSymbol :: forall x y . (TL.KnownSymbol x, TL.KnownSymbol y) => Proxy x -> Proxy y -> SingT (TL.CmpSymbol x y)
compareSymbol x y =  
  let trustMe :: forall a b . a :~: b 
      trustMe = unsafeCoerce (Refl :: () :~: ())
  in case compare (TL.symbolVal x) (TL.symbolVal y) of 
       LT -> case trustMe :: TL.CmpSymbol x y :~: 'LT of { Refl -> SLT }
       EQ -> case trustMe :: TL.CmpSymbol x y :~: 'EQ of { Refl -> SEQ }
       GT -> case trustMe :: TL.CmpSymbol x y :~: 'GT of { Refl -> SGT }



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

--
type family UniqueOrdered (xs :: [Symbol]) :: Constraint where 
  UniqueOrdered '[] = () 
  UniqueOrdered '[ a ] = () 
  UniqueOrdered (a ': b ': r) = (TL.CmpSymbol a b ~ LT, UniqueOrdered (b ': r))

type UniqueOrderedLabels xs = UniqueOrdered (RecLabels xs) 

-- Lookup a value in a list of rec labels 
type family LookupRec (xs :: [RecLabel Symbol k]) (x :: Symbol) :: k where 
  LookupRec ( (nm ::: ty) ': rest ) nm' = CaseOrdering (TL.CmpSymbol nm nm') (LookupRec rest nm') ty (LookupRec rest nm') 

type family LookupIx (xs :: [k]) (i :: TL.Nat) :: k where 
  LookupIx ( x ': xs ) 0 = x 
  LookupIx ( x ': xs ) n = LookupIx xs (n TL.- 1)

lookupRec :: forall (xs :: [RecLabel Symbol b]) (nm :: Symbol) (r :: b) . (LookupRec xs nm ~ r) => Prod SingT xs -> SingT nm -> SingT r 
lookupRec PNil x = x `seq` error "lookupSing: impossible" 
-- lookupRec (PCons (SRecLabel nm ty) rest) nm' = 
--   case undefined of -- compareSymbol' (SingT nm) (SingT nm') of 
--     SEQ -> ty 
--     SLT -> lookupRec rest nm' 
--     SGT -> lookupRec rest nm' 

        
-- List 
prod2sing :: Prod SingT xs -> SingT xs 
prod2sing = undefined 
-- prod2sing PNil = SNil 
-- prod2sing (PCons x xs) = SCons x (prod2sing xs)

sing2prod :: SingT xs -> Prod SingT xs 
sing2prod = undefined 
-- sing2prod SNil = PNil 
-- sing2prod (SCons x xs) = x :> sing2prod xs 

{-
data instance SingT (x :: [k]) where 
  SNil :: SingT '[] 
  SCons :: !(SingT x) -> !(SingT xs) -> SingT (x ': xs) 
type ListSing = (SingT :: [k] -> *) 
instance All Sing xs => Sing xs where sing = prod2sing $ mkProdC (Proxy :: Proxy Sing) sing 

instance (DecideEq (SingT :: k -> *)) => DecideEq (SingT :: [k] -> *) where 
  SNil %== SNil = Just Refl 
  SCons x xs %== SCons y ys = liftA2 (cong2 Refl) (x %== y) (xs %== ys) 
  _ %== _ = Nothing 
-}

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
