
module Options (Options(..),getOptions,usageInfo',verboseLn,verbose)
where
--import List                  (isSuffixOf)
import System                (getArgs, getProgName, exitFailure)
import System.Environment    (getEnvironment)
import Languages (Lang(..))
import Char (toUpper)
import System.Console.GetOpt
import System.FilePath
import System.Directory
--import System.FilePath.Posix
-- | This data constructor is able to hold all kind of information that is useful to 
--   express what the user would like ADL to do. 
data Options = Options { contextName   :: Maybe String
                       , showVersion   :: Bool
                       , showHelp      :: Bool
        --             , verbose       :: String -> IO ()  -- vervangt putStr -- Voor de fijnproevers: Een functie kan hier ook! ;-)) 
		--			   , verboseLn     :: String -> IO ()  -- vervangt putStrLn
					   , verboseP      :: Bool
					   , genPrototype  :: Bool 
					   , uncheckedDirPrototype  :: Maybe String
					   , dirPrototype  :: String
					   , allServices   :: Bool
					   , dbName        :: Maybe String
					   , genAtlas      :: Bool
					   , uncheckedDirAtlas      :: Maybe String
					   , dirAtlas      :: String
					   , genXML        :: Bool
					   , fspec         :: Bool
					   , proofs        :: Bool
					   , haskell       :: Bool
					   , uncheckedDirOutput     :: Maybe String
					   , dirOutput     :: String     
					   , beeper        :: Bool
					   , crowfoot      :: Bool
					   , language      :: Lang
                       , progrName     :: String
                       , adlFileName   :: String
                       , baseName      :: String
                       , logName       :: String
                       , uncheckedLogName :: Maybe String
                       , services      :: Bool
                       } deriving Show
 
getOptions :: IO Options
getOptions = 
   do args     <- getArgs
      progName <- getProgName
      env      <- getEnvironment
      flags    <- case getOpt Permute options args of
                      (o,[n],[])    -> return (foldl (flip id) (defaultOptions env n progName) o )
                      (_,[],[] )    -> ioError (userError ("no file to parse" ++usageInfo' progName))
                      (_,x:xs,[])   -> ioError (userError ("too many files: "++ show [x:xs] ++usageInfo' progName))
                      (_,_,errs)    -> ioError (userError (concat errs ++ usageInfo' progName))
      flags'   <- checkPaths flags
      return flags'

checkPaths :: Options -> IO Options
checkPaths flags = 
        do flags0  <- case uncheckedLogName flags of
                          Nothing -> return flags { logName = "ADL.log"}
                          Just s  -> return flags { logName = s } 
           verboseLn flags0 ("Checking output directories...")
           currDir <- getCurrentDirectory
           flags1  <- case uncheckedDirOutput flags0 of
                          Nothing -> return flags0 { dirOutput = currDir }
                          Just s  -> do exists <- doesDirectoryExist s
                                        if exists
                                          then return flags0 { dirOutput =  s}
                                          else ioError (userError ("Directory does not exist: "++s))  
           flags2 <- if genPrototype flags1
                        then case uncheckedDirPrototype flags1 of
                             Nothing -> return flags1 { dirPrototype = dirOutput flags1 }
                             Just s  -> do exists <- doesDirectoryExist s
                                           if exists
                                             then return flags1 { dirPrototype = s }
                                             else ioError (userError ("Directory does not exist: "++s))
                        else return flags1  {- No need to check if no prototype will be generated. -}
           flags3 <- if genAtlas flags2
                        then case uncheckedDirAtlas flags2 of
                             Nothing -> return flags2 { dirAtlas = dirOutput flags2 }
                             Just s  -> do exists <- doesDirectoryExist s
                                           if exists
                                             then return flags2 { dirAtlas = s }
                                             else ioError (userError ("Directory does not exist: "++s))
                        else return flags2  {- No need to check if no atlas will be generated. -}
           return flags3                  
             



      
usageInfo' :: String -> String
usageInfo' progName = usageInfo (infoHeader progName) options
          
infoHeader :: String -> String
infoHeader progName = "\nUsage info:\n " ++ progName ++ " options file ...\n\nList of options:"




options     :: [OptDescr (Options -> Options)]
options  = [ Option ['C']     ["context"]      (OptArg contextOpt "name")  "use context with name"
           , Option ['v']     ["version"]      (NoArg versionOpt)          "show version and exit"
           , Option ['h','?'] ["help"]         (NoArg helpOpt)             "get (this) usage information"
           , Option []        ["verbose"]      (NoArg verboseOpt)          "verbose error message format"
           , Option ['p']     ["proto"]        (OptArg prototypeOpt "dir") ("generate a functional prototype with services defined in the ADL file (dir overrides "++
                                                                                envdirPrototype ++ " )") 
           , Option ['P']     ["maxServices"]  (NoArg maxServicesOpt)      "if specified, generate all services in the prototype"
           , Option ['d']     ["dbName"]       (OptArg dbNameOpt "name")   ("use database with name (name overrides "++
                                                                                envdbName ++ " )")
           , Option ['s']     ["services"]     (NoArg servicesOpt)         "generate service specifications in ADL format"
           , Option ['a']     ["atlas"]        (OptArg atlasOpt "dir" )    ("generate atlas (optional an output directory, defaults to current directory) (dir overrides "++
                                                                                envdirAtlas ++ " )")
           , Option []        ["XML"]          (NoArg xmlOpt)              "generate XML output"
           , Option []        ["fspec"]        (NoArg fspecOpt)            "generate a functional specification document"
           , Option []        ["proofs"]       (NoArg proofsOpt)           "generate correctness proofs"
           , Option []        ["haskell"]      (NoArg haskellOpt)          "generate internal data structure, written in Haskell source code (for debugging)"
           , Option ['o']     ["outputDir"]    (ReqArg outputDirOpt "dir") ("default directory for generated files (dir overrides "++
                                                                                envdirOutput ++ " )")        
           , Option []        ["beeper"]       (NoArg beeperOpt)           "generate beeper instead of checker"
           , Option []        ["crowfoot"]     (NoArg crowfootOpt)         "generate crowfoot notation in graphics"
           , Option []        ["language"]     (ReqArg languageOpt "lang") "language to be used, ('NL' or 'UK')"
           , Option ['l']     ["log"]          (ReqArg logOpt "name")       ("log to file with name (name overrides "++
                                                                                envlogName  ++ " )")
           ]

defaultOptions :: [(String, String)] -> String -> String -> Options
defaultOptions env fName pName 
               = Options { contextName   = Nothing
                         , showVersion   = False
                         , showHelp      = False
                   --      , verbose       = donothing
			       --      , verboseLn     = donothing
			             , verboseP      = False
			             , genPrototype  = False
					     , uncheckedDirPrototype  = lookup envdirPrototype env
            		     , dirPrototype  = unchecked
            		     , allServices   = False
		                 , dbName        = lookup "CCdbName" env
		                 , genAtlas      = False   
            		     , uncheckedDirAtlas      = lookup envdirAtlas env
            		     , dirAtlas      = unchecked
            		     , genXML        = False 
	            	     , fspec         = False
	            	     , proofs        = False
	            	     , haskell       = False
	            	     , uncheckedDirOutput     = lookup envdirOutput env
                         , dirOutput     = unchecked
                         , beeper        = False
                         , crowfoot      = False
                         , language      = Dutch
                         , progrName     = pName
                         , adlFileName   = replaceExtension fName ".adl"
                         , baseName      = dropExtension  fName
                         , uncheckedLogName = lookup envlogName env
                         , logName       = "ADL.log"
                         , services      = False
                         }
                    
envdirPrototype = "CCdirPrototype"
envdirAtlas="CCdirAtlas"
envdirOutput="CCdirOutput"
envdbName="CCdbName"
envlogName="CClogName"

contextOpt  nm  opts = opts{contextName  = nm}            
versionOpt      opts = opts{showVersion  = True}            
helpOpt         opts = opts{showHelp     = True}            
verboseOpt      opts = opts{ -- verbose      = putStr
                            --,verboseLn    = putStrLn
                            verboseP     = True}            
prototypeOpt nm opts = opts{uncheckedDirPrototype = nm
                           ,genPrototype = True}
maxServicesOpt  opts = opts{genPrototype = True
                           ,allServices  = True}                            
dbNameOpt nm    opts = opts{dbName       = nm}
atlasOpt nm     opts = opts{uncheckedDirAtlas     =  nm
                           ,genAtlas     = True}
xmlOpt          opts = opts{genXML       = True}
fspecOpt        opts = opts{fspec        = True}
proofsOpt       opts = opts{proofs       = True}
servicesOpt     opts = opts{services     = True}
haskellOpt      opts = opts{haskell      = True}
outputDirOpt nm opts = opts{uncheckedDirOutput    = Just nm}
beeperOpt       opts = opts{beeper       = True}
crowfootOpt     opts = opts{crowfoot     = True}
languageOpt l   opts = opts{language     = case map toUpper l of
                                             "NL"      -> Dutch
                                             "UK"      -> English
                                             otherwise -> Dutch}
logOpt nm       opts = opts{uncheckedLogName = Just nm} 
verbose flags x
    | verboseP flags = putStr x
    | otherwise      = donothing
   
verboseLn flags x
    | verboseP flags = putStrLn x
    | otherwise      = donothing
    
donothing = putStr ""   -- Ik weet zo gauw niet hoe dit anders moet....
unchecked = "."
                             