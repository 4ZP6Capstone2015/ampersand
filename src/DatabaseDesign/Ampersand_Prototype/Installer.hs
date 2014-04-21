{-# OPTIONS_GHC -Wall #-}
module DatabaseDesign.Ampersand_Prototype.Installer
  (installer,createDatabasePHP,createTablesPHP,plug2tbl,dropplug,historytbl,sessiontbl,CreateTable) where

import Data.List
import Data.Maybe
import DatabaseDesign.Ampersand_Prototype.CoreImporter
import DatabaseDesign.Ampersand_Prototype.RelBinGenBasics(indentBlock,commentBlock,addSlashes,phpIndent,showPhpStr, quote, sqlAtomQuote)
import DatabaseDesign.Ampersand_Prototype.RelBinGenSQL(selectExprRelation,sqlRelPlugs)
import DatabaseDesign.Ampersand_Prototype.Version 

fatal :: Int -> String -> a
fatal = fatalMsg "Installer"


--  import Debug.Trace

installer :: Fspc -> Options -> String
installer fSpec flags = intercalate "\n  "
   (
      [ "<!DOCTYPE html PUBLIC \"-//W3C//DTD HTML 4.0 Strict//EN\">"
      , "<html>"
      , "<head>"
      , "<meta http-equiv=\"Content-Type\" content=\"text/html; charset=UTF-8\"/>"
      , ""
      , "<meta http-equiv=\"Pragma\" content=\"no-cache\">"
      , "<meta http-equiv=\"no-cache\">"
      , "<meta http-equiv=\"Expires\" content=\"-1\">"
      , "<meta http-equiv=\"cache-Control\" content=\"no-cache\">"
      , ""
      , "</html>"
      , "<body>"
      ,"<?php"
      , "// Try to connect to the database\n"
      , "if(isset($DB_host)&&!isset($_REQUEST['DB_host'])){"
      , "  $included = true; // this means user/pass are probably correct"
      , "  $DB_link = @mysqli_connect(@$DB_host,@$DB_user,@$DB_pass,@$DB_name);"
      , "}else{"
      , "  $included = false; // get user/pass from some place else"
      , "  if(file_exists(\"dbSettings.php\")) include \"dbSettings.php\";"
      , "  else { // no settings found.. try some default settings"
      , "    if(!( $DB_link=@mysqli_connect($DB_host='"++addSlashes (sqlHost flags)++"',$DB_user='"++addSlashes (sqlLogin flags)++"',$DB_pass='"++addSlashes (sqlPwd flags)++"',$DB_name='"++addSlashes (dbName flags)++"')))"
      , "    { // we still have no working settings.. ask the user!"
      , "      die(\"Install failed: cannot connect to MySQL\"); // todo" --todo
      , "    }"
      , "  } "
      , "}"
      , "if($DB_slct = @mysqli_select_db('"++dbName flags++"')){"
      , "  $existing=true;"
      , "}else{"
      , "  $existing = false; // db does not exist, so try to create it" ] ++
      indentBlock 2 (createDatabasePHP (dbName flags))  ++
      [ "  $DB_slct = @mysqli_select_db('"++dbName flags++"');"
      , "}"
      , "if(!$DB_slct){"
      , "  echo die(\"Install failed: cannot connect to MySQL or error selecting database '"++dbName flags++"'\");" --todo: full error report
      , "}else{"
      ] ++ indentBlock 2
      (
        [ "if(!$included && !file_exists(\"dbSettings.php\")){ // we have a link now; try to write the dbSettings.php file"
        , "   if($fh = @fopen(\"dbSettings.php\", 'w')){"
        , "     fwrite($fh, '<'.'?php $DB_link=mysqli_connect($DB_host=\"'.$DB_host.'\", $DB_user=\"'.$DB_user.'\", $DB_pass=\"'.$DB_pass.'\", $DB_name=\"'.$DB_name.'\"); $DB_debug = 3; ?'.'>');"
        , "     fclose($fh);"
        , "   }else die('<P>Error: could not write dbSettings.php, make sure that the directory of Installer.php is writable"
        , "              or create dbSettings.php in the same directory as Installer.php"
        , "              and paste the following code into it:</P><code>'."
        , "             '&lt;'.'?php $DB_link=mysqli_connect($DB_host=\"'.$DB_host.'\", $DB_user=\"'.$DB_user.'\", $DB_pass=\"'.$DB_pass.'\", $DB_name=\"'.$DB_name.'\"); $DB_debug = 3; ?'.'&gt;</code>');"
        , "}\n"
        , "$error=false;" ] ++
        createTablesPHP fSpec ++
        ["mysqli_query($DB_link,'SET TRANSACTION ISOLATION LEVEL SERIALIZABLE');" ] ++
        -- TODO: why set this only for the next transaction? (no SESSION or GLOBAL parameter is provided)
    
        ["if ($err=='') {"
        ,"  echo '<div id=\"ResetSuccess\"/>The database has been reset to its initial population.<br/><br/><button onclick=\"window.location.href = document.referrer;\">Ok</button>';"
        ,"  $content = '"
        ,"  <?php"
        ,"  require \"Generics.php\";"
        ,"  require \"php/DatabaseUtils.php\";"
        ,"  $dumpfile = fopen(\"dbdump.adl\",\"w\");"
        ,"  fwrite($dumpfile, \"CONTEXT "++name fSpec++"\\n\");"
        ]
        ++
        ["  fwrite($dumpfile, dumprel(\""++name d++showSign (sign d)++"\",\""++qry++"\"));" 
        | d<-relsDefdIn fSpec, decusr d
        , let dbrel = case sqlRelPlugs fSpec (EDcD d) of
                        [] -> fatal 82 "null dbrel"
                        x  -> x
        , let (_,srcField,trgField) = head dbrel
        , let qry = selectExprRelation fSpec (-1) (fldname srcField) (fldname trgField) d]
        ++
        ["  fwrite($dumpfile, \"ENDCONTEXT\");"
        ,"  fclose($dumpfile);"
        ,"  "
        ,"  function dumprel ($rel,$quer)"
        ,"  {"
        ,"    $rows = DB_doquer($quer);"
        ,"    $pop = \"\";"
        ,"    foreach ($rows as $row)"
        ,"      $pop = $pop.\";(\\\"\".escapedoublequotes($row[0]).\"\\\",\\\"\".escapedoublequotes($row[1]).\"\\\")\\n  \";"
        ,"    return \"POPULATION \".$rel.\" CONTAINS\\n  [\".substr($pop,1).\"]\\n\";"
        ,"  }"
        ,"  function escapedoublequotes($str) { return str_replace(\"\\\"\",\"\\\\\\\\\\\\\"\",$str); }"
        ,"  ?>';"
        ,"  file_put_contents(\"dbdump.php.\",$content);"  
        ,"}"]
       ) ++
       [ "}"
       , "\n?></body></html>\n" ]
    ) 

createDatabasePHP :: String ->[String]
createDatabasePHP nm = ["@mysqli_query("++showPhpStr ("CREATE DATABASE `"++nm++"` DEFAULT CHARACTER SET UTF8")++");"]

createTablesPHP :: Fspc ->[String]
createTablesPHP fSpec =
        [ "/*** Create new SQL tables ***/"
        , ""
        , "// Session timeout table"
        , "if($columns = mysqli_query($DB_link,"++showPhpStr ("SHOW COLUMNS FROM `__SessionTimeout__`")++")){"
        , "    mysqli_query($DB_link,"++showPhpStr ("DROP TABLE `__SessionTimeout__`")++");"
        , "}"
        ] ++ createTablePHP 21 sessiontbl ++
        [ "if($err=mysqli_error($DB_link)) {"
        , "  $error=true; echo $err.'<br />';"
        , "}"
        , "" 
        , "// Timestamp table"
        , "if($columns = mysqli_query($DB_link,"++showPhpStr ("SHOW COLUMNS FROM `__History__`")++")){"
        , "    mysqli_query($DB_link,"++showPhpStr ("DROP TABLE `__History__`")++");"
        , "}"
        ] ++ createTablePHP 21 historytbl ++
        [ "if($err=mysqli_error($DB_link)) {"
        , "  $error=true; echo $err.'<br />';"
        , "}"
        , "$time = explode(' ', microTime()); // copied from DatabaseUtils setTimestamp"
        , "$microseconds = substr($time[0], 2,6);"
        , "$seconds =$time[1].$microseconds;"
        , "date_default_timezone_set(\"Europe/Amsterdam\");" 
        -- to prevent a php warning TODO: check if this is ok when Ampersand is used in different timezones 
        , "$date = date(\"j-M-Y, H:i:s.\").$microseconds;" 
        , "mysqli_query($DB_link,\"INSERT INTO `__History__` (`Seconds`,`Date`) VALUES ('$seconds','$date')\");"
        , "if($err=mysqli_error($DB_link)) {"
        , "  $error=true; echo $err.'<br />';"
        , "}"
        , ""
        , "//// Number of plugs: " ++ show (length (plugInfos fSpec))
        , "if($existing==true){"
        ] ++ indentBlock 2 (concatMap checkPlugexists (plugInfos fSpec))
        ++ ["}"]
        ++ concatMap plugCode [p | InternalPlug p <- plugInfos fSpec]
  where plugCode plug
         = commentBlock (["Plug "++name plug,"","fields:"]++map (\x->showADL (fldexpr x)++"  "++show (multiplicities $ fldexpr x)) (plugFields plug))
           ++ createTablePHP 17 (plug2tbl plug)
           ++ ["if($err=mysqli_error($DB_link)) { $error=true; echo $err.'<br />'; }"]
           ++ case tblcontents (gens fSpec) (initialPops fSpec) plug of
               [] -> []
               tblRecords -> [ "else"
                             , "mysqli_query($DB_link,"++showPhpStr ("INSERT IGNORE INTO "++quote (name plug)
                                                           ++" ("++intercalate "," [quote (fldname f) |f<-plugFields plug]++")"
                                                           ++phpIndent 17++"VALUES " ++ intercalate (phpIndent 22++", ") [ "(" ++valuechain md++ ")" | md<-tblRecords]
                                                           ++phpIndent 16 )
                                        ++");"
                             ]
                             ++ ["if($err=mysqli_error($DB_link)) { $error=true; echo $err.'<br />'; }"]
        valuechain record = intercalate ", " [case fld of Nothing -> "NULL" ; Just str -> sqlAtomQuote str | fld<-record]
        checkPlugexists (ExternalPlug _) = []
        checkPlugexists (InternalPlug plug)
         = [ "if($columns = mysqli_query($DB_link,"++showPhpStr ("SHOW COLUMNS FROM "++quote (name plug)++"")++")){"
           , "  mysqli_query($DB_link,"++showPhpStr (dropplug plug)++");" --todo: incremental behaviour
           , "}" ]



-- (CREATE TABLE name, fields, engine)
type CreateTable = (String,[String],String)

createTablePHP :: Int -> CreateTable -> [String] 
createTablePHP i (crtbl,crflds,crengine)
         = [ "mysqli_query($DB_link,\""++ crtbl]
           ++ indentBlock i crflds
           ++ [replicate i ' ' ++ crengine ++ "\");"]
           
plug2tbl :: PlugSQL -> CreateTable
plug2tbl plug
 = ( "CREATE TABLE "++quote (name plug)++""
   , [ comma: " "++quote (fldname f)++" " ++ showSQL (fldtype f) ++ (if fldauto f then " AUTO_INCREMENT" else " DEFAULT NULL") 
     | (f,comma)<-zip (plugFields plug) ('(':repeat ',') ]++
      case (plug, plugFields plug) of
           (BinSQL{}, _) -> []
           (_,    plg:_) -> [", PRIMARY KEY (`"++fldname plg++"`)"]
           _             -> []
   , ") ENGINE=InnoDB DEFAULT CHARACTER SET UTF8")

dropplug :: PlugSQL -> String
dropplug plug = "DROP TABLE "++quote (name plug)++""

historytbl :: CreateTable
historytbl
 = ( "CREATE TABLE `__History__`"
   , [ "( `Seconds` VARCHAR(255) DEFAULT NULL"
     , ", `Date` VARCHAR(255) DEFAULT NULL"]
   , ") ENGINE=InnoDB DEFAULT CHARACTER SET UTF8")

sessiontbl :: CreateTable
sessiontbl
 = ( "CREATE TABLE `__SessionTimeout__`"
   , [ "( `SESSION` VARCHAR(255) UNIQUE NOT NULL"
     , ", `lastAccess` BIGINT NOT NULL"]
   , ") ENGINE=InnoDB DEFAULT CHARACTER SET UTF8")
