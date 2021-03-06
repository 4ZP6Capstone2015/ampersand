module Main (main) where

import Database.Design.Ampersand.Misc.Options(getOptions,Options)
import Database.Design.Ampersand.Test.TestScripts (getTestScripts,testAmpersandScripts)
import Database.Design.Ampersand.Test.Parser.ParserTest (parseScripts)
import Database.Design.Ampersand.Test.Parser.QuickChecks (parserQuickChecks)
import System.Exit (ExitCode, exitFailure, exitSuccess)

testFunctions :: Options -> IO [([String], IO Bool)]
testFunctions opts =
    do scr <- getTestScripts
       (parserCheckResult, msg) <- parserQuickChecks
       return [ (["Parsing " ++ show (length scr) ++ " scripts."], parseScripts opts scr)
            --  , ("Executing ampersand chain", ampersand scr)
              , ( if parserCheckResult  
                  then ["Parser & prettyprinter test PASSED."]
                  else (  ["QuickCheck found errors in the roundtrip in parsing/prettyprinting for the following case:"]
                        ++map ("\n   "++) (lines msg)
                       )
                , return parserCheckResult
                )
              ]

main :: IO ExitCode
main = do opts <- getOptions
          funcs <- testFunctions opts
          testAmpersandScripts
          tests funcs
    where tests :: [([String], IO Bool)] -> IO ExitCode
          tests [] = exitSuccess
          tests ((msg,test):xs) =
            do mapM_ putStrLn msg
               success <- test
               if success then tests xs
               else do putStrLn "*** Something went wrong here***" 
                       exitFailure
