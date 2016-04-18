{-# LANGUAGE ScopedTypeVariables, TypeOperators, PolyKinds #-} 
{-# OPTIONS -fno-warn-unticked-promoted-constructors #-} 
{-# OPTIONS -fno-warn-orphans #-} 

-- Various utilities related to type level equality 

module Database.Design.Ampersand.ECA2SQL.Equality 
  ( cong, cong2, cong3
  , Dict(..)
  , Exists(..), (#>>) 
  , Not, elimNeg, triviallyTrue, mapNeg, doubleneg
  , Void, Dec(..), DecEq, mapDec, dec2bool, liftDec2
  , module Data.Type.Equality
  , module GHC.Exts 
  , safeCoerce
  ) where 

import GHC.Exts (Constraint)
import Data.Type.Equality ((:~:)(..))
import Control.DeepSeq 
import Unsafe.Coerce 
import Database.Design.Ampersand.Basics.Assertion

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
data Dict p where Dict :: p => Dict p -- patern matched will return a proof of p; where p is a class restraint like show; can write things like Dict Eq list -> Dict List; it will figure it out via pattern matching

-- Existence proof 
data Exists p where Ex :: p x -> Exists p

infixr 3 #>>
(#>>) :: Exists p -> (forall x . p x -> r) -> r
(#>>) (Ex x) f = f x

-- Strict negation. A value of type `Not p' is never inhabited by `\x ->
-- ... _|_ ...'. If you have `x :: Not p' and `y :: p` then
-- you can be sure that `elimNot x p' is *really* a proof of `Void'. 
-- Since it is a newtype, it is also not inhabited by `_|_' itself. 

newtype Not a = Not_ (a -> Void) 

-- This is valid only if the interface doesn't violate the assumed 
-- semantics
instance NFData (Not a) where 
  rnf (Not_ f) = f `seq` () 

doubleneg :: NFData a => a -> Not (Not a)
doubleneg x = x `deepseq` Not_ $ \y -> elimNeg y x 

-- primitive constructor of negation without any unsafecoerce
triviallyTrue :: Not (Not ())
triviallyTrue = doubleneg ()  

mapNeg :: (NFData a, NFData b) => (b -> a) -> Not a -> Not b 
mapNeg f (Not_ q) = Not_ $ q `deepseq` (\x -> q (f $!! x)) 

elimNeg :: NFData a => Not a -> a -> Void 
elimNeg (Not_ f) a = f $!! a

-- "Real" decidable equality. 
data Void 
instance Show Void where 
  show x = case x of {} 

data Dec p where 
  Yes :: !p -> Dec p  -- !p is a strict value of p that is not bottom
  No  :: !(Not p) -> Dec p  -- other wise it is not p, a value of dec p => exclude middle holds 

instance Show (Dec p) where 
  show = \case { Yes{} -> "Yes"; No{} -> "No" } 

type DecEq a b = Dec (a :~: b) 

mapDec :: (p -> q) -> (Not p -> Not q) -> Dec p -> Dec q
mapDec yes _ (Yes x) = Yes (yes x) 
mapDec _ no (No y) = No (no y) 

liftDec2 :: Dec p -> Dec q -> (p -> q -> r) -> (Not p -> Not r) -> (Not q -> Not r) -> Dec r 
liftDec2 (Yes p) (Yes q) yes _ _ = Yes (yes p q) 
liftDec2 (No p) _ _ no _ = No (no p) 
liftDec2 _ (No p) _ _ no = No (no p)

dec2bool :: DecEq a b -> Bool
dec2bool = \case { Yes{} -> True; No{} -> False } 
 

-- for debugging  
safeCoerce :: String -> a -> b
safeCoerce str _ = error $ "unsafeCoerce:" ++ str
