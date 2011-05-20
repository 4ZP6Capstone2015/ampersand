{-# OPTIONS_GHC -Wall #-}
module DatabaseDesign.Ampersand_Prototype.Version
  (ampersandPrototypeVersionBanner, versionNumberPrototype, fatalMsg)
where
import DatabaseDesign.Ampersand_Prototype.CoreImporter (versionNumber)
ampersandPrototypeVersionBanner :: String
ampersandPrototypeVersionBanner = "Prototype vs. "++versionNumberPrototype++ "(core vs. "++versionNumber++")"

fatalMsg :: String -> Int -> String -> a
fatalMsg haskellModuleName lineNr msg
 = error ("!fatal "++show lineNr++" (module "++haskellModuleName++", "++ampersandPrototypeVersionBanner++")\n  "++msg)

versionNumberPrototype :: String
versionNumberPrototype = "2.0.1.925" -- #1.#2.#3.#4 : #1 major version; #2 student release version; #3 production fix version (normally 0 ); #4 SVN revision number.
{-
SVN Version text:
Ticket #96 is fixed. 
Also made the export structure of ampersand library module more strict. 
This version is compilable with Ampersand vs. 2.1.0.70
-}
