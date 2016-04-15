{-# LANGUAGE PatternSynonyms,ScopedTypeVariables, TypeOperators, PolyKinds #-}
--{-# OPTIONS -fno-warn-unticked-promoted-constructors #-}
{-# OPTIONS -fno-warn-orphans #-}

-- Various utilities related to type level equality

module Database.Design.Ampersand.ECA2SQL.EqualityTest
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
--import Database.Design.Ampersand.ECA2SQL.Trace
import Control.Monad (unless)
import Data.List (stripPrefix)
import System.Exit (exitFailure)
import Test.QuickCheck.All (quickCheckAll)
import Database.Design.Ampersand.ECA2SQL.Trace
import Data.List
import Data.Bits
import Data.Bool
import Data.Foldable
import Data.Void
import Database.Design.Ampersand.ECA2SQL.Equality
import Test.QuickCheck 
import Control.Monad

 ------basics---------
rev_iso :: [Int] -> Bool
rev_iso xs =(reverse.reverse) xs == xs

idem:: [Int] -> Bool
idem xs = sort xs == (sort.sort) xs

revmap::Blind(Int->String)->[Int]->Bool
revmap (Blind f) xs = (reverse.map f) xs == (map f . reverse) xs

--putStrLn::String->IO()
--putStr "Basic Tests passed"
 ----Equality.hs------
--tDdict :: Dict Eq xs -> Dict ys -> Bool
--tDdict xs ys = Dict (TestList xs) == Dict (TestList ys) --should show eq; both type list

tmapDec :: mapDec a b (Yes x) -> Property
tmapDec yes y (Yes x) = mapDec yes y (Yes x) == mapDec (mapDec yes y (Yes x))

tdec2bool :: a -> b -> (f->a) -> (f->b) -> Property
tdec2bool Yes Yes =  dec2bool Yes Yes == dec2bool(dec2bool Yes Yes) Yes

tdoubleneg :: (f->a) -> Property
tdoubleneg x = doubleneg x == doubleneg (doubleneg x) 

--double negative = positive, 2 positives is a positive
-- map (* (-1)) [1,2,3,4] = [-1,-2,-3,-4] == [-1,-2,-3,-4]
--sanity check

triviallytrue:: x -> f x -> Property
ttriviallytrue x = triviallytrue Not (Not a) == triviallytrue a

-- tmapneg (+2) [] == mapNeg (+2) Void == mapNeg (mapNeg (+2) Void) -- absurd :: Void -> a

elimNegtest :: f a -> (f->b) -> b -> Bool
-- elimNeg a (Not a) b = absurd (elimNeg a (Not a) b) == absurd (elimNeg a (Not a) b)

-- Void values logically dont exist; witness to logical reasoning

testsafeCoerce :: String -> (f->a) -> Int -> String

tsafeCoerce "abc" = safeCoerce "abc" a == safeCoerce "abc" (safeCoerce "abc" a)

---- use collect for lenghts to get stats for quickcheck?
newtype TestList a = TestList {getList :: [a]}
                     deriving (Eq, Show)

instance (Arbitrary a, Integral a) =>
    Arbitrary (TestList a) where
        arbitrary = TestList <$> oneof [
                    return []
                   , liftM2 (:)
                        arbitrary
                        (liftM getList arbitrary)
                   ]
