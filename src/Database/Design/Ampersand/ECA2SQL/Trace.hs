{-# LANGUAGE PatternSynonyms, NoMonomorphismRestriction, OverloadedStrings, LambdaCase, EmptyCase #-} 
{-# LANGUAGE ViewPatterns, ScopedTypeVariables, PolyKinds, UndecidableInstances, DataKinds, DefaultSignatures #-}
{-# LANGUAGE PartialTypeSignatures, TypeOperators #-} 
{-# OPTIONS -fno-warn-unticked-promoted-constructors #-} 

-- Various utilities used by ECA2SQL 

module Database.Design.Ampersand.ECA2SQL.Trace 
  ( module Database.Design.Ampersand.ECA2SQL.Trace 
  , module Numeric.Natural
  , assert 
  ) where 

import Control.DeepSeq
import Numeric.Natural (Natural)
import Control.Exception (assert, try, Exception, AssertionFailed(..))
import System.IO.Unsafe

-- proper trace messages 
data TraceInfo 
  = TraceInfo { trLocLine :: Natural, trLocColRange :: (Natural, Natural), trCtx :: String } 
    deriving (Show, Eq) 

takePrefix :: Eq a => [a] -> [a] -> Maybe [a]
takePrefix [] xs = Just xs 
takePrefix _  [] = Nothing 
takePrefix (x:xs) (y:ys)
  | x == y    = takePrefix xs ys 
  | otherwise = Nothing  

-- Maybe because if optimizations are on, `assert' doesn't do anything. 
getTraceInfo :: (Bool -> IO () -> IO ()) -> IO (Maybe TraceInfo)
getTraceInfo assert_ = do 
  let parseMsg :: String -> TraceInfo 
      parseMsg msg0 = 
        let (ctx, (':':msg2)) = span (/=':') msg0
            (locLine, (':':msg3)) = span (/=':') msg2 
            (colStart, ('-':msg4)) = span (/='-') msg3 
            (colEnd, _) = span (/=':') msg4 
        in TraceInfo (read locLine) (read colStart, read colEnd) ctx 

  merr <- try $ assert_ False (return ())
  return $ either (Just . parseMsg . (\(AssertionFailed m) -> m)) (const $ Nothing) merr 

{-# INLINE failure #-} 
failure :: (Bool -> IO () -> IO ()) -> (Maybe TraceInfo -> String) -> a 
failure assert_ f = unsafePerformIO $ do 
  i <- getTraceInfo assert_
  return (error (f i)) 

{-# INLINE impossible #-} 
impossible :: NFData b => (Bool -> IO () -> IO ()) -> String -> b -> a 
impossible assert_ nm toeval = deepseq toeval $ deepseq nm $ failure assert_ mkmsg where 
  baseMsg = "The impossible occured" ++ concat [ ": "++nm | not (null nm) ] ++ "." 
  mkmsg Nothing = baseMsg
  mkmsg (Just (TraceInfo (show -> ln) ((show -> cfr), (show -> cto)) ctx)) = concat
    [ baseMsg, "\n  at line ", ln, ", columns ", cfr, " - " , cto, " in module ", ctx ]
                            

