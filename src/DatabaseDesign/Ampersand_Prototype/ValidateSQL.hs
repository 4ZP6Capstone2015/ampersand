{-# OPTIONS_GHC -Wall #-}
module DatabaseDesign.Ampersand_Prototype.ValidateSQL (validateRulesSQL)

where

import Data.List
import Data.Maybe
import Control.Monad
import System.Process
import System.Exit
import System.IO hiding (hPutStr,hGetContents)
import System.Directory
import DatabaseDesign.Ampersand_Prototype.CoreImporter hiding (putStr, origin)
import DatabaseDesign.Ampersand_Prototype.RelBinGenBasics
import DatabaseDesign.Ampersand_Prototype.RelBinGenSQL
import DatabaseDesign.Ampersand_Prototype.Installer
import DatabaseDesign.Ampersand_Prototype.Version 
import Control.Exception
import Prelude hiding (exp)

{-
Validate the generated SQL for all rules in the fSpec, by comparing the evaluation results
with the results from Haskell-based Ampersand rule evaluator. The latter is much simpler and
therefore most likely to be correct in case of discrepancies.
-}

fatal :: Int -> String -> a
fatal = fatalMsg "ValidateSQL"

tempDbName :: String
tempDbName = "TemporaryValidationDatabase"

validateRulesSQL :: Fspc -> Options -> IO Bool
validateRulesSQL fSpec flags =
 do { when (any (not.isSignal.fst) (allViolations fSpec)) 
        (do { putStrLn "The population would violate invariants. Could not generate your database."
            ; exitWith $ ExitFailure 10
                 })
    ; hSetBuffering stdout NoBuffering
    
    ; putStrLn "Initializing temporary database"
    ; createTempDatabase fSpec flags
     
    ; let allExps = getAllInterfaceExps fSpec ++ 
                    getAllRuleExps fSpec ++
                    getAllPairViewExps fSpec ++
                    getAllIdExps fSpec ++
                    getAllViewExps fSpec
                    
    ; putStrLn $ "Number of expressions to be validated: "++show (length allExps)
    ; results <- mapM (validateExp fSpec flags) allExps 
                   
--    ; putStrLn "\nRemoving temporary database"
--    ; removeTempDatabase flags
    
    ; case [ ve | (ve, False) <- results] of
        [] -> do { putStrLn "\nValidation successful.\nWith the provided populations, all generated SQL code has passed validation."
                 ; return True
                 }
        ves -> do { putStrLn ( "\n\nValidation error. The following expressions failed validation:\n" ++
                               unlines (map showVExp ves)
                             )
                  ; return False
                  } 
    }


-- functions for extracting all expressions from the context

getAllInterfaceExps :: Fspc -> [ValidationExp]
getAllInterfaceExps fSpec = concat [ getObjExps (name ifc) $ ifcObj ifc 
                                   | ifc <- interfaceS fSpec ++ interfaceG fSpec ]
 where getObjExps iName objDef = (objctx objDef, "interface " ++ show iName) :
                                 concatMap (getObjExps iName) (attributes objDef)

-- we check the complement of the rule, since that is the expression evaluated in the prototype
getAllRuleExps :: Fspc -> [ValidationExp]
getAllRuleExps fSpec = map getRuleExp $ vrules fSpec ++ grules fSpec
 where getRuleExp rule = (notCpl (rrexp rule), "rule "++show (name rule))
 
getAllPairViewExps :: Fspc -> [ValidationExp]
getAllPairViewExps fSpec = concatMap getPairViewExps $ vrules fSpec ++ grules fSpec
 where getPairViewExps r@Ru{rrviol = Just (PairView pvsegs)} =
         [ (exp, "violation view for rule "++show (name r)) | PairViewExp _ exp <- pvsegs ]
       getPairViewExps _    = []              

getAllIdExps :: Fspc -> [ValidationExp]
getAllIdExps fSpec = concatMap getIdExps $ vIndices fSpec
 where getIdExps identity = [ (objctx objDef, "identity "++show (name identity)) 
                            | IdentityExp objDef <- identityAts identity ]

getAllViewExps :: Fspc -> [ValidationExp]
getAllViewExps fSpec = concatMap getViewExps $ vviews fSpec
 where getViewExps view = [ (objctx objDef, "view "++show (name view)) 
                          | ViewExp objDef <- vdats view ]

type ValidationExp = (Expression, String) 
-- a ValidationExp is an expression together with the place in the context where we 
-- obtained it from (e.g. rule/interface/..)
showVExp :: ShowADL a => (a, String) -> String
showVExp (exp, origin) = "Origin: "++origin++", expression: "++showADL exp

-- validate a single expression and report the results
validateExp :: Fspc -> Options -> ValidationExp -> IO (ValidationExp, Bool)
validateExp _     _    vExp@(EDcD{}, _)   = -- skip all simple relations 
 do { putStr "."
    ; return (vExp, True)
    }
validateExp fSpec flags vExp@(exp, origin) =
 do { --putStr $ "Checking "++origin ++": expression = "++showADL exp
    ; violationsSQL <- fmap sort . evaluateExpSQL fSpec flags $ exp
    ; let violationsAmp = sort $ fullContents (gens fSpec) (initialPops fSpec) exp
    
    ; if violationsSQL == violationsAmp 
      then 
       do { putStr "." -- ++show violationsSQL
          ; return (vExp, True)
          }    
      else
       do { putStr $ "Checking "++origin ++": expression = "++showADL exp
          ; putStrLn "\nMismatch between SQL and Ampersand"
          ; putStrLn $ showVExp vExp
          ; putStrLn $ "SQL violations:\n"++show violationsSQL
          ; putStrLn $ "Ampersand violations:\n" ++ show violationsAmp
          ; return (vExp, False)
          }
    }

-- evaluate normalized exp in SQL
evaluateExpSQL :: Fspc -> Options -> Expression -> IO [(String,String)]
evaluateExpSQL fSpec flags exp =
  fmap sort (performQuery flags violationsQuery)
 where violationsExpr = conjNF exp
       violationsQuery = selectExpr fSpec 26 "src" "tgt" violationsExpr
  
performQuery :: Options -> String -> IO [(String,String)]
performQuery flags queryStr =
 do { queryResult <- (executePHP . showPHP) php 
    ; if "Error" `isPrefixOf` queryResult -- not the most elegant way, but safe since a correct result will always be a list
      then do verboseLn flags{verboseP=True} ("\n******Problematic query:\n"++queryStr++"\n******")
              fatal 141 $ "PHP/SQL problem: "++queryResult
      else case reads queryResult of
             [(pairs,"")] -> return pairs
             _            -> fatal 143 $ "Parse error on php result: "++show queryResult
    }
   where
    php = 
      [ "// Try to connect to the database"
      , "$DB_name='"++addSlashes tempDbName++"';"
      , "global $DB_host,$DB_user,$DB_pass;"
      , "$DB_host='"++addSlashes (sqlHost flags)++"';"
      , "$DB_user='"++addSlashes (sqlLogin flags)++"';"
      , "$DB_pass='"++addSlashes (sqlPwd flags)++"';"
      , "$DB_link = mysqli_connect($DB_host,$DB_user,$DB_pass,$DB_name);"
      , "// Check connection"
      , "if (mysqli_connect_errno()) {"
      , "  die(\"Error: Failed to connect to $DB_name: \" . mysqli_connect_error());"
      , "}"
      , ""
      , "$sql="++showPhpStr queryStr++";"
      , "$result=mysqli_query($DB_link,$sql);"
      , "if(!$result)"
      , "  die('Error '.($ernr=mysqli_errno($DB_link)).': '.mysqli_error($DB_link).'(Sql: $sql)');"
      , "$rows=Array();"
      , "  while (($row = @mysqli_fetch_array($result))!==false) {"
      , "    $rows[]=$row;"
      , "    unset($row);"
      , "  }"
      , "echo '[';"
      , "for ($i = 0; $i < count($rows); $i++) {"
      , "  if ($i==0) echo ''; else echo ',';"
      , "  echo '(\"'.addslashes($rows[$i]['src']).'\", \"'.addslashes($rows[$i]['tgt']).'\")';"
      , "}"
      , "echo ']';"
      ]

createTempDatabase :: Fspc -> Options -> IO ()
createTempDatabase fSpec flags =
 do { _ <- executePHP php
    ; return ()
    }
 where 
  php = showPHP 
     ([ "// Try to connect to the database"
      , "$DB_name='"++addSlashes tempDbName++"';"
      , "global $DB_host,$DB_user,$DB_pass;"
      , "$DB_host='"++addSlashes (sqlHost flags)++"';"
      , "$DB_user='"++addSlashes (sqlLogin flags)++"';"
      , "$DB_pass='"++addSlashes (sqlPwd flags)++"';"
      
      , "$DB_link = mysqli_connect($DB_host,$DB_user,$DB_pass);"
      , "// Check connection"
      , "if (mysqli_connect_errno()) {"
      , "  die(\"Failed to connect to MySQL: \" . mysqli_connect_error());"
      , "}"
      , ""
      , "// Drop the database if it exists"
      , "$sql=\"DROP DATABASE $DB_name\";"
      , "mysqli_query($DB_link,$sql);"
      , "// Don't bother about the error if the database didn't exist..."
      , ""
      , "// Create the database"
      , "$sql=\"CREATE DATABASE $DB_name DEFAULT CHARACTER SET UTF8\";"
      , "if (!mysqli_query($DB_link,$sql)) {"
      , "  die(\"Error creating the database: \" . mysqli_error($DB_link));"
      , "  }"
      , ""
      , "// Connect to the freshly created database"
      , "$DB_link = mysqli_connect($DB_host,$DB_user,$DB_pass,$DB_name);"
      , "// Check connection"
      , "if (mysqli_connect_errno()) {"
      , "  die(\"Failed to connect to the database: \" . mysqli_connect_error());"
      , "  }"
      , ""
      ]++
      createTablesPHP fSpec
     )

connectToServer :: Options -> [String]
connectToServer flags =
  ["$DB_link = mysqli_connect('"++addSlashes (sqlHost flags)++"'"
                         ++",'"++addSlashes (sqlLogin flags)++"'"
                         ++",'"++addSlashes (sqlPwd flags)++"');"] 
               
-- call the command-line php with phpStr as input
executePHP :: String -> IO String
executePHP phpStr =
 do { --putStrLn $ "Executing PHP:\n" ++ phpStr
    ; tempdir <- catch getTemporaryDirectory
                       (\e -> do let err = show (e :: IOException)
                                 hPutStr stderr ("Warning: Couldn't find temp directory. Using current directory : " ++ err)
                                 return ".")

    ; (tempfile, temph) <- openTempFile tempdir "phpInput"
    ; hPutStr temph phpStr
    ; hClose temph
     
    ; let cp = CreateProcess
                { cmdspec      = RawCommand "php" [tempfile]
                , cwd          = Nothing -- path
                , env          = Just [("TERM","dumb")] -- environment
                , std_in       = Inherit 
                , std_out      = CreatePipe
                , std_err      = CreatePipe
                , close_fds    = False -- no need to close all other file descriptors
                , create_group = False
                }
            
    ; (_, mStdOut, mStdErr, _) <- createProcess cp 
    ; outputStr <-
        case (mStdOut, mStdErr) of
          (Nothing, _) -> fatal 105 "no output handle"
          (_, Nothing) -> fatal 106 "no error handle"
          (Just stdOutH, Just stdErrH) ->
           do { --putStrLn "done"
              ; errStr <- hGetContents stdErrH
              ; seq (length errStr) $ return ()
              ; hClose stdErrH
              ; unless (null errStr) $
                  putStrLn $ "Error during PHP execution:\n" ++ errStr 
              ; outputStr' <- hGetContents stdOutH --and fetch the results from the output pipe
              ; seq (length outputStr') $ return ()
              ; hClose stdOutH
              ; return outputStr'
              }
    ; removeFile tempfile
--    ; putStrLn $ "Results:\n" ++ outputStr
    ; return outputStr
    }
    
showPHP :: [String] -> String
showPHP phpLines = unlines $ ["<?php"]++phpLines++["?>"]
