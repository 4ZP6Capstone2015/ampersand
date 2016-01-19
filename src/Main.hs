module Main where

import Control.Monad
import Data.List
import Data.Function (on)
import System.Exit
import Prelude hiding (putStr,readFile,writeFile)
import Database.Design.Ampersand.Prototype.ObjBinGen   (generatePhp, writeStaticFiles)
import Database.Design.Ampersand.Core.AbstractSyntaxTree
import Database.Design.Ampersand
import Database.Design.Ampersand.Prototype.GenBericht  (doGenBericht)
import Database.Design.Ampersand.Prototype.Generate    (generateGenerics)
import Database.Design.Ampersand.Output.ToJSON.ToJson  (generateJSONfiles)
import Database.Design.Ampersand.Prototype.GenFrontend (doGenFrontend, clearTemplateDirs)
import Database.Design.Ampersand.Prototype.ValidateSQL (validateRulesSQL)
import Database.Design.Ampersand.ECA2SQL.PrettyPrinterSQL (eca2PrettySQL)
import Text.PrettyPrint.Leijen (Pretty(..))
import qualified Text.PrettyPrint.Leijen as P
import Text.Printf (printf) 
import Control.Exception (catch, Handler(..), ErrorCall(..), IOException, SomeException(..), AssertionFailed(..), throwIO
                         , Exception(..))
import qualified Data.Typeable as Typ

main :: IO ()
main =
 do opts@Options{printECAInfo} <- getOptions
    if showVersion opts || showHelp opts
    then mapM_ putStr (helpNVersionTexts ampersandVersionStr opts)
    else do gFSpec <- createFSpec opts
            case gFSpec of
              Errors err    -> do putStrLn "Error(s) found:"
                                  mapM_ putStrLn (intersperse  (replicate 30 '=') (map showErr err))
                                  exitWith $ ExitFailure 10
              Checked fSpec -> do when printECAInfo $ printECAInfoFSPec fSpec 
                                  generateAmpersandOutput  fSpec
                                  generateProtoStuff       fSpec




-- -I ../ampersand-models/Examples/ProjectAdministration -o ../ampersand-models/Examples/ProjectAdministration ProjectAdministration.adl --print-eca-info
printECAInfoFSPec :: FSpec -> IO ()  
printECAInfoFSPec fSpec@FSpec{..} = do
  let opts = getOpts 
      printSep x = print x >> putStrLn (replicate 15 '=') 
      reallyShowADL :: ECArule -> String 
      reallyShowADL (ECA trgr param cls ruleN) = show $ P.vsep  
        [ P.text "ECA Rule #" P.<> P.int ruleN 
        , P.hsep [ P.text "ON", P.text (show trgr), P.text "INTO", P.text (show param), P.text "DO" ]
        , P.nest 4 $ P.vsep $ map P.text $ lines $ showADL cls 
        ] 
             
      -- Deal with exceptions by printing them and continuing for testing purposes
      handleExceptions :: String -> IO () -> IO () 
      handleExceptions nm ac = catch ac hndlr where 
          allowedExcpts = [ Typ.typeOf (undefined :: IOException) 
                          , Typ.typeOf (undefined :: ErrorCall) 
                          , Typ.typeOf (undefined :: AssertionFailed) 
                          ]
          hndlr (SomeException e) = do 
            let allowed = Typ.typeOf e `elem` allowedExcpts 
            printf "An%s exception of %s (of type %s) occured while trying to evaluate [%s]\n" 
              (if allowed then "" else " unexpected") (show e) (show $ Typ.typeOf e) nm 
            when (not allowed) (throwIO e) 
            

  handleExceptions "name" $ do 
    putStrLn $ "The name of the specification is " ++ fsName 

  handleExceptions "validateSQL" $ do 
    validatedRules <- validateRulesSQL fSpec 
    putStrLn $ "Output of specification :" ++ show validatedRules -- ++ rulename ++'\n' ++ "SQL Rules" ++ validatedSQLRules 
    putStrLn $ "Violations:" ++ "Rule Violated:" ++ show grules ++ "\t" ++ show vrules 

  let violationsOfInvariants :: [(Rule,[AAtomPair])]
      violationsOfInvariants
        = [(r,vs) |(r,vs) <- allViolations
                  , not (isSignal r)
          ]
      reportViolations :: [(Rule,[AAtomPair])] -> IO()
      reportViolations []    = verboseLn getOpts "No violations found."
      reportViolations viols =
        let ruleNamesAndViolStrings = [ (name r, showprs p) | (r,p) <- viols ]
        in  putStrLn $ intercalate "\n"
                         [ "Violations of rule "++show r++":\n"++ concatMap (\(_,p) -> "- "++ p ++"\n") rps
                         | rps@((r,_):_) <- groupBy (on (==) fst) $ sort ruleNamesAndViolStrings
                         ]

      showprs :: [AAtomPair] -> String
      showprs aprs = "["++intercalate ", " (map showADL aprs)++"]"

  handleExceptions "invariants" $ do 
    reportViolations violationsOfInvariants
    maybe (putStrLn "No test rule.") id $ ruleTest fSpec <$> testRule getOpts 
  
  handleExceptions "concept tables" $ do 
    putStrLn $ "All SQL concept tables"
    mapM_ print $ 
      [(plug,att) |InternalPlug plug@TblSQL{}<-plugInfos, (_,att)<-cLkpTbl plug]++
      [(plug,att) |InternalPlug plug@BinSQL{}<-plugInfos, (_,att)<-cLkpTbl plug]++
      [(plug,sqlColumn plug) |InternalPlug plug@ScalarSQL{}<-plugInfos] 

  handleExceptions "eca - hs" $ 
    putStrLn "ECA rules [ Haskell ]" >> mapM_ (putStrLn . showHS opts "") vEcas

  handleExceptions "eca - hs" $ 
    putStrLn "ECA rules [ ADL ]" >> mapM_ (putStrLn . reallyShowADL) vEcas

  putStrLn "ECA rules [ SQL ]" 
  mapM_ (\eca -> handleExceptions ("eca" ++ show (ecaNum eca) ++ " - hs") . printSep . eca2PrettySQL fSpec $ eca) vEcas 
  
  

generateProtoStuff :: FSpec -> IO ()
generateProtoStuff fSpec
-- HJO: The following has been commented out, because:
-- 1) it does not seem to be used
-- 2) It's purpose is unclear
-- 3) underlying code has been modified. It is unclear what that would mean for this functionality
--     ==> Hence, we have bitrot.
--  | Just nm <- validateEdit (getOpts fSpec) =
--      do { verboseLn (getOpts fSpec) "Validating edit operations:"
--         ; gBeforePops <- getPopulationsFrom (getOpts fSpec) $ nm ++ ".before.pop"
--         ; gAfterPops <- getPopulationsFrom (getOpts fSpec) $ nm ++ ".after.pop"
--         ; case (,) <$> gBeforePops <*> gAfterPops of
--              Errors err -> do putStrLn "Error(s) found in before/after populations:"
--                               mapM_ putStrLn (intersperse  (replicate 30 '=') (map showErr err))
--                               exitWith $ ExitFailure 10
--              Checked (beforePops, afterPops) ->
--               do { isValid <- validateEditScript fSpec beforePops afterPops (nm++".edit.json")
--                  ; unless isValid (exitWith (ExitFailure 30))
--                  }
--         }
  | validateSQL (getOpts fSpec) =
      do { verboseLn (getOpts fSpec) "Validating SQL expressions..."
         ; isValid <- validateRulesSQL fSpec
         ; unless isValid (exitWith (ExitFailure 30))
         }
  | otherwise =
      do { when (genPrototype (getOpts fSpec)) $ doGenProto fSpec
         ; when (genBericht (getOpts fSpec))   $ doGenBericht fSpec
         ; case testRule (getOpts fSpec) of
             Just ruleName -> ruleTest fSpec ruleName
             Nothing       -> return ()
    ; when ((not . null . allViolations) fSpec && (development . getOpts) fSpec ) $
        verboseLn (getOpts fSpec) "\nWARNING: There are rule violations (see above). The database might be invalid."
    ; verboseLn (getOpts fSpec) "Done."  -- if there are violations, but we generated anyway (ie. with --dev), issue a warning
    }

doGenProto :: FSpec -> IO ()
doGenProto fSpec =
 do { verboseLn (getOpts fSpec) "Checking on rule violations..."
    ; reportViolations violationsOfInvariants
    ; reportSignals (initialConjunctSignals fSpec)
    ; if null violationsOfInvariants || development (getOpts fSpec)
      then do { verboseLn (getOpts fSpec) "Generating prototype..."
              ; clearTemplateDirs fSpec
              ; writeStaticFiles (getOpts fSpec)
              ; generatePhp fSpec
              ; generateGenerics fSpec
              ; generateJSONfiles fSpec
              ; doGenFrontend fSpec
              ; verboseLn (getOpts fSpec) "\n"
              ; verboseLn (getOpts fSpec) $ "Prototype files have been written to " ++ dirPrototype (getOpts fSpec)
              }
      else do { putStrLn "\nERROR: No prototype generated because of rule violations.\n(Compile with --dev to generate a prototype regardless of violations)"
              ; exitWith $ ExitFailure 40
              }
    }
 where violationsOfInvariants :: [(Rule,[AAtomPair])]
       violationsOfInvariants
         = [(r,vs) |(r,vs) <- allViolations fSpec
                   , not (isSignal r)
           ]
       reportViolations :: [(Rule,[AAtomPair])] -> IO()
       reportViolations []    = verboseLn (getOpts fSpec) "No violations found."
       reportViolations viols =
         let ruleNamesAndViolStrings = [ (name r, showprs p) | (r,p) <- viols ]
         in  putStrLn $ intercalate "\n"
                          [ "Violations of rule "++show r++":\n"++ concatMap (\(_,p) -> "- "++ p ++"\n") rps
                          | rps@((r,_):_) <- groupBy (on (==) fst) $ sort ruleNamesAndViolStrings
                          ]

       showprs :: [AAtomPair] -> String
       showprs aprs = "["++intercalate ", " (map showADL aprs)++"]"
       -- showpr :: AAtomPair -> String
       -- showpr apr = "( "++(showVal.apLeft) apr++", "++(showVal.apRight) apr++" )"
       reportSignals []        = verboseLn (getOpts fSpec) "No signals for the initial population."
       reportSignals conjViols = verboseLn (getOpts fSpec) $ "Signals for initial population:\n" ++ intercalate "\n"
         [   "Rule(s): "++(show . map name . rc_orgRules) conj
         ++"\n  Conjunct   : " ++ showADL (rc_conjunct conj)
         ++"\n  Violations : " ++ showprs viols
         | (conj, viols) <- conjViols
         ]
ruleTest :: FSpec -> String -> IO ()
ruleTest fSpec ruleName =
 case [ rule | rule <- grules fSpec ++ vrules fSpec, name rule == ruleName ] of
   [] -> putStrLn $ "\nRule test error: rule "++show ruleName++" not found."
   (rule:_) -> do { putStrLn $ "\nContents of rule "++show ruleName++ ": "++showADL (rrexp rule)
                  ; putStrLn $ showContents rule
                  ; let rExpr = rrexp rule
                  ; let ruleComplement = rule { rrexp = notCpl (EBrk rExpr) }
                  ; putStrLn $ "\nViolations of "++show ruleName++" (contents of "++showADL (rrexp ruleComplement)++"):"
                  ; putStrLn $ showContents ruleComplement
                  }
 where showContents rule = let pairs = [ "("++(show.showValADL.apLeft) v++"," ++(show.showValADL.apRight) v++")" | (r,vs) <- allViolations fSpec, r == rule, v <- vs]
                           in  "[" ++ intercalate ", " pairs ++ "]"
