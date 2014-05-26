{-# LANGUAGE CPP #-}
{-# OPTIONS_GHC -Wall #-}
module DatabaseDesign.Ampersand_Prototype.ObjBinGen  (phpObjInterfaces) where
 
import DatabaseDesign.Ampersand_Prototype.Installer           (installerDBstruct,installerDefPop,dumpPopulationToADL)
import DatabaseDesign.Ampersand_Prototype.RelBinGenBasics     (addSlashes)
import DatabaseDesign.Ampersand_Prototype.Apps
import DatabaseDesign.Ampersand_Prototype.Generate            (generateAll)
import Control.Monad
import System.FilePath               
import System.Directory
import qualified Data.ByteString as Bin
import DatabaseDesign.Ampersand_Prototype.CoreImporter  
import Prelude hiding (writeFile,readFile,getContents)


import DatabaseDesign.Ampersand_Prototype.StaticFiles_Generated
#ifdef MIN_VERSION_MissingH 
import System.Posix.Files  -- If MissingH is not available, we are on windows and cannot set file 
import System.Time

import Data.Time.Clock.POSIX
#endif

phpObjInterfaces :: Fspc -> Options -> IO()
phpObjInterfaces fSpec flags =
 do { writeStaticFiles flags
    ; verboseLn flags "---------------------------"
    ; verboseLn flags "Generating php Object files with Ampersand"
    ; verboseLn flags "---------------------------"
    ; write "InstallerDBstruct.php"     (installerDBstruct fSpec flags)
    ; write "InstallerDefPop.php"       (installerDefPop fSpec )
    ; write "DumpPopulationToADL.php"   (dumpPopulationToADL fSpec)
    
    ; let dbSettingsFilePath = combine targetDir "dbSettings.php"
    ; dbSettingsExists <- doesFileExist dbSettingsFilePath
    -- we generate a dbSettings.php only if it does not exist already.
    ; if dbSettingsExists
      then verboseLn flags "  Using existing dbSettings.php."
      else do { verboseLn flags "  Writing dbSettings.php."
              ; writeFile dbSettingsFilePath dbsettings
              }

    ; generateAll fSpec flags          
    ; when (genAtlas flags) $ doGenAtlas fSpec flags
    ; verboseLn flags "\n"
    }
   where
    write fname content =
     do { verboseLn flags ("  Generating "++fname)
        ; writeFile (combine targetDir fname) content
        }
    dbsettings = unlines
       [ "<?php"
       , ""
       , "global $DB_host,$DB_user,$DB_pass;"
       , "$DB_host='"++addSlashes (sqlHost flags)++"';"
       , "$DB_user='"++addSlashes (sqlLogin flags)++"';"
       , "$DB_pass='"++addSlashes (sqlPwd flags)++"';"
       , ""
       , "$DB_link=mysqli_connect($DB_host, $DB_user, $DB_pass)"
       , "      or exit(\"Error connecting to the database: username / password are probably incorrect.\");"
       , ""
       , "?>"
       ]
    targetDir = dirPrototype flags

doGenAtlas :: Fspc -> Options -> IO()
doGenAtlas fSpec flags =
 do { verboseLn flags "Installing the Atlas application:"
    ; verboseLn flags ("Importing "++show (importfile flags)++" into namespace "++ show (namespace flags) ++" of the Atlas ...")
    ; verboseLn flags ("The atlas application should have been installed in " ++ show (dirPrototype flags) ++ ".")
    ; fillAtlas fSpec flags
    }             
                
writeStaticFiles :: Options -> IO()
writeStaticFiles flags =
  if genStaticFiles flags
  then 
 do {
#ifdef MIN_VERSION_MissingH 
      verboseLn flags "Updating static files"
#else
      verboseLn flags "Writing static files"
#endif
    ; sequence_ [ writeWhenMissingOrOutdated flags sf (writeStaticFile flags sf) | sf <- allStaticFiles ]
    }
  else
      verboseLn flags "Skipping static files (because of command line argument)"
          
writeWhenMissingOrOutdated :: Options -> StaticFile -> IO () -> IO ()
writeWhenMissingOrOutdated flags staticFile act =
#ifdef MIN_VERSION_MissingH 
 do { exists <- doesFileExist $ absFilePath flags staticFile 
    ; if exists then
       do { oldTimeStamp <- getModificationTime $ absFilePath flags staticFile
          ; if oldTimeStamp < timeStamp staticFile then
             do { verboseLn flags $ "  Replacing static file "++ filePath staticFile ++" with current version."
                ; act
                }
            else
              return () -- skip is not really worth logging
          }
      else
       do { verboseLn flags $ "  Writing static file "++ filePath staticFile
          ; act
          }
    }       
#else
-- On windows we cannot set the file modification time without requiring a cygwin or mingw build environment,
-- so we simply replace all static files on each generation.
 do { verboseLn flags $ "  Writing static file "++ filePath staticFile
    ; act
    }
#endif
                                    
writeStaticFile :: Options -> StaticFile -> IO()
writeStaticFile flags sf = 
  do { createDirectoryIfMissing True (takeDirectory (absFilePath flags sf))
     ; write (absFilePath flags sf) (contentString sf) 
#ifdef MIN_VERSION_MissingH 
     ; let t = (fromIntegral . fromEnum . utcTimeToPOSIXSeconds) (timeStamp sf)
     ; setFileTimes (absFilePath flags sf) t t
#endif
     }
 where write a b = if isBinary sf 
                   then Bin.writeFile a (read b)
                   else writeFile a b

absFilePath :: Options -> StaticFile -> FilePath
absFilePath flags sf = combine (dirPrototype flags) (filePath sf)
