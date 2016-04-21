{-# LANGUAGE ImplicitParams, ViewPatterns #-}

-- | Assertions with better error message and handling of bottom values 
module Database.Design.Ampersand.Basics.Assertion  
  (impossible, Justification(..), justify, NFData(..)) where

import GHC.Stack
import GHC.SrcLoc
import Control.DeepSeq 
import Data.String 

data Justification 
  = Justification [String] 
  | NoJustification 

justify :: r -> ([String] -> r) -> Justification -> r
justify none just = \case 
  Justification x -> just x 
  NoJustification -> none 

-- | Allows the argument to `impossible' to be a string literal. 
instance IsString Justification where 
  fromString = Justification . words 


-- | Modified from `GHC.Stack.showCallStack'
showCallStackTop :: CallStack -> String
showCallStackTop ((reverse.getCallStack) -> (root:_))
  = showCallSite root where showCallSite (f, loc) = f ++ ", called at " ++ showSrcLoc loc
showCallStackTop _ = error "CallStack cannot be empty!"

-- | A function which evaluates its arguements to normal form before asserting
--   that the evaluation of this expression is an error. The error message 
--   contains location information about the function which used `impossible' 
--   The supplied argument is an optional "reasoning" for why the case is impossible. 
impossible :: (?loc :: CallStack, NFData x) => Justification -> x -> a
impossible mbErrMsg deps = 
  deps `deepseq` error errMsg where 
    errMsg = unlines $ 
      [ "Somebody asserted that this case is impossible" ++ justify "." (const " because") mbErrMsg 
      ] ++ map ("  "++) (justify [] id mbErrMsg) ++ 
      [ "The error occured at:" , showCallStackTop ?loc ] 
      
