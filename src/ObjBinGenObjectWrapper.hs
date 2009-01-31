  module ObjBinGenObjectWrapper where
   import Char
   import Auxiliaries
   import Calc(informalRule, disjNF, computeOrder, ComputeRule, triggers)
   import CC_aux
   import CommonClasses
   import PredLogic -- (for error messages by dbCorrect)
   import Hatml     -- (for converting error messages to HTML)
   import Atlas     -- (for converting error messages to HTML)
   import RelBinGenBasics (phpIdentifier)
  

   objectWrapper objectName
    = (chain "\n  "
      ([ "<?php // generated with ADL"
       , ""
       , "require \"localsettings.inc.php\";"
       , "require \""++objectName++".inc.php\";"
       , ""
       , "$view = new view(parseRequest(getObject_"++phpIdentifier objectName++"()),getObject_"++phpIdentifier objectName++"());"
       , "$view->display();"
       , ""
       ]
      )) ++ "?>"
