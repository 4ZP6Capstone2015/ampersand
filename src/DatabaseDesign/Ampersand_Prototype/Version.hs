{-# OPTIONS_GHC -Wall #-}
module Database.Design.Ampersand_Prototype.Version (prototypeVersionStr, fatalMsg) where 

import Database.Design.Ampersand_Prototype.BuildInfo_Generated
import Database.Design.Ampersand_Prototype.CoreImporter (ampersandVersionStr, ampersandVersionWithoutBuildTimeStr)


fatalMsg :: String -> Int -> String -> a
fatalMsg haskellModuleName lineNr msg
 = error ("!fatal "++show lineNr++" (module "++haskellModuleName++", "++prototypeVersionWithoutBuildtimeStr++")\n  "++msg)
 -- Please do not print anything in between "!fatal " and the line number that follows. So do not turn this into "!fatal error " for example.
 -- Why? The error message says for instance "fatal 384", which can be ^C'ed and used for searching within the editor.

prototypeVersionStr :: String
prototypeVersionStr = prototypeOnlyVersionStr++", build time: "++buildTimeStr++ " (lib: "++ampersandVersionStr++")"

prototypeVersionWithoutBuildtimeStr :: String
prototypeVersionWithoutBuildtimeStr = prototypeOnlyVersionStr ++ " (lib: "++ampersandVersionWithoutBuildTimeStr++")"

prototypeOnlyVersionStr :: String
prototypeOnlyVersionStr = "Prototype v"++cabalVersionStr++"."++svnRevisionStr
{- 
   #1.#2.#3.#4 : #1 major version; #2 student release version; #3 production fix version (normally 0 ); 
   #4 SVN revision number: 
      - may be a range separated by ':' if the working copy contains mixed revisions (e.g. "163:165")
      - ends with an 'M' if the working copy was modified (e.g. "163M")
      - for other (rare) values, see the output of the command 'svnversion --help' 
-}
