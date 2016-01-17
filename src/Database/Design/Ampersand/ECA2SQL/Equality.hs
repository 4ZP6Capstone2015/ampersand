{-# LANGUAGE ScopedTypeVariables, TypeOperators, PolyKinds #-} 
{-# OPTIONS -fno-warn-unticked-promoted-constructors #-} 
{-# OPTIONS -fno-warn-orphans #-} 

-- Various utilities related to type level equality 

module Database.Design.Ampersand.ECA2SQL.Equality 
  ( cong, cong2, cong3
  , Dict(..)
  , Exists(..), (#>>) 
  , Not, elimNeg, triviallyFalse, triviallyTrue, mapNeg, notfalsum
  , type (==) 
  , Void, Dec(..), DecEq, mapDec, dec2bool 
  , module Data.Type.Equality
  , module GHC.Exts 
  ) where 

import GHC.Exts (Constraint)
import Data.Type.Equality ((:~:)(..))
import Control.DeepSeq 
import Unsafe.Coerce 

-- Manipulating equality proofs 
cong :: f :~: g -> a :~: b -> f a :~: g b 
cong Refl Refl = Refl 

cong2 :: f :~: g -> a :~: a' -> b :~: b' -> f a b :~: g a' b' 
cong2 Refl Refl Refl = Refl 

cong3 :: f :~: g -> a :~: a' -> b :~: b' -> c :~: c' -> f a b c :~: g a' b' c' 
cong3 Refl Refl Refl Refl = Refl 

-- DeepSeq
instance NFData (a :~: b) where rnf Refl = () 

-- Reify a class as a value
data Dict p where Dict :: p => Dict p 

-- Existence proof 
data Exists p where Ex :: p x -> Exists p

infixr 3 #>>
(#>>) :: Exists p -> (forall x . p x -> r) -> r
(#>>) (Ex x) f = f x

-- Type level equality. This allows us to (unsafely) derive
-- a decision procedure for (~). 
type family (==) (a :: k) (b :: k) :: Bool where 
  (==) a a = 'True 
  (==) a b = 'False 

triviallyFalse :: ((a == b) ~ 'False) => Not (a :~: b) 
triviallyFalse = Not_ ( \case{} )

triviallyTrue :: forall a b . ((a == b) ~ 'True) => a :~: b 
triviallyTrue = unsafeCoerce (Refl :: a :~: a) -- TRUST ME 

-- Strict negation. A value of type `Not p' is never inhabited by `\x ->
-- ... undefined ...'. If you have `x :: Not p' and `y :: p` then
-- you can be sure that `elimNot x p' is *really* a proof of `Void'. 
-- Since it is a newtype, it is also not inhabited by `undefined'.

newtype Not a = Not_ (a -> Void) 

notfalsum :: NFData a => Void -> Not a 
notfalsum v = Not_ (\x -> rnf x `seq` v)

mapNeg :: NFData b => (b -> a) -> Not a -> Not b 
mapNeg f (Not_ q) = Not_ (\x -> q (f $!! x)) 

elimNeg :: Not a -> a -> Void 
elimNeg (Not_ f) a = f a

-- "Real" decidable equality. 
data Void 
instance Show Void where 
  show x = case x of {} 

data Dec p where 
  Yes :: !p -> Dec p 
  No  :: !(Not p) -> Dec p 

instance Show (Dec p) where 
  show = \case { Yes{} -> "Yes"; No{} -> "No" } 

type DecEq a b = Dec (a :~: b) 

mapDec :: (p -> q) -> (Not p -> Not q) -> Dec p -> Dec q
mapDec yes _ (Yes x) = Yes (yes x) 
mapDec _ no (No y) = No (no y) 

dec2bool :: DecEq a b -> Bool
dec2bool = \case { Yes{} -> True; No{} -> False } 
