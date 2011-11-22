<?php
error_reporting(E_ALL^E_NOTICE); 
ini_set("display_errors", 1);

require "Interfaces.php"; 
// defines $dbName, $isDev, $relationTableInfo, $allInterfaceObjects, and $rulesSql

require "php/DatabaseUtils.php";

echo '<div id="UpdateResults">';
//emitLog('ja');
//emitLog('ja');
//emitAmpersandErr('Rule was broken!');
//error('zaza');

dbStartTransaction($dbName);
emitLog('BEGIN');

processCommands();

if (checkRules()) {
  emitLog('COMMIT');
  dbCommitTransaction($dbName);
} else {
  emitLog('ROLLBACK');
  dbRollbackTransaction($dbName);
}

echo '</div>';



/*
// todo:
 * 
 * 
TODO: CHECK EDIT BEHAVIOR AND SQL PROPERTIES ON ROWS (see 'Bespreken met Stef.txt')

 
ticket 138
todo: move to php dir
todo: remove test errors for update to x and delete Pino
todo: a php error should also cause rollback, so perhaps we do need to collect php results, rather than echoing them.
todo: implement navigation arrow from old prototype?
todo: does Atom Atom in computeDbCommands also match descendants? (eg. .. ATOM .. atom .. ATOM ..)
todo: modified atom values are not escaped
todo: maybe don't use column unique and not null, since these might be weaker than the multiplicities (sometimes a surjective relation will allow nulls, depending on other relations in the same table, although possibly the table prop generator is wrong and will contain non-null in that case)
todo: box shadow gebruiken?
todo: header always at top? probably makes it easier to float error windows

todo: click anywhere should disable navigation context menu
todo: figure out how to do editing when interfaces are floating horizontally at some level (e.g. in Viro)
todo: sqlRelPlugNames also returns list. Change to maybe?

insert goes wrong if we have [keyA, keyB, keyC] and insert (valA1,valB1) (valA2,valB2), since unique keyC will contain 2 nulls.
kind of a pathoemitLogical case, since tuples for valA1 will most likely be inserted before any valA2 tuples.

field editable also if it has children in an editable relation

another problem is that if the interface leaves certain fields null, then multiple inserts (which are rare) will cause a sql error
rather than a rule failing.
 
If stable atom is not unique, but modified is, do we want an update? Could be useful, but is kind of vague.

make example with multiple relations, all in one table
check delete and insert on that


BUG: empty list has insert button to the left, or is this ok?

support editing on interface atom (also possible in old prototype)
what happens when we change it? does it even make sense? what if interface is not a relation and subinterfaces are neither?
what happens when we change an atom that has subinterfaces? explicitly update those subinterfaces? (if they have a (flip)relation)
maybe on modification, always also update subinterfaces that are relations. If the table width already causes the update, no harm is done, but
if table width does not cause update, unexpected behavior may occur. e.g. if rel1 is same table as parent relation, but rel2 isn't, then a [rel1: b, rel2:c] ~> aa [rel1:b, rel2:c] will cause (a,b)~>(aa,b), but not (a,c)~>(aa,c)

support make new stuff. (generate unique? or ask user? both are not that hard) 

update is delete+insert does not work, as delete removes all attributes in row, so add update edit op

check for double atom names

checking presence of the atom and replacing it can be combined in a single query

fix univalency and atomic container/ atomlist container. is a bit messy now.

maybe not insert template & stub when not editing or no relation present

use better way to access/update concept table

insert is not optimized at all: 
  rows could be grouped together
  insert into concept table may be executed repeatedly
  
insert atom into multiple concept tables?


setNavigationHandlers now sets colors. We should set an attr, so the colors can be specified in css
// use POST for db updates, now commands are in the url, preventing refresh from working
// can we use this somewhere? $_SERVER['PHP_SELF']
// relation & concept with equal name cause name clash? table names are not case sensitive (or does quoting help?)

// handle double events when clicking on a button (insert, delete, cancel, commit, etc.) while editing a text field (strangely enough the blur event arrives later)

Newly inserted Identifier atom goes wrong when we navigate to it (maybe related to absence in id[Thing]

Later: css content can acces attributes, so we don't need to put the Insert new .. string in the generator. it can be put in the css

*/

/*

insertNew insert new tuple in relation. Check if id[concept(new)] contains new, if not, the concept is new and the table we edited was not its concept-list table, so insert
delete put null in deleted target (so we need a dest here too). Check if id[concept(new)] contains new, if not, we are in the concept-list table and accidentally removed the concept, so insert
update is combination of the above


probably easy to support editing on I[Concept], V[ONE*Concept], and V[Concept,ONE] (maybe we don't need the latter though)
When editing I[Concept], inserting is easy, but what about delete? First check all columns of all tables that contain Concept?

cleanup post mechanism a bit, so we don't send the whole page on a post (only need to send the AmpersandRoot div)

*/

function processCommands() {  
  global $dbName; 
  $commandsJson =$_POST['commands']; 
  if (isset($commandsJson)) {
    $commandArray = json_decode($commandsJson);
          
    foreach ($commandArray as $command)
      processCommand($command);
       
  }
}

function processCommand($command) {
  if (!isset($command->dbCmd))
    error("Malformed command, missing 'dbCmd'");

  switch ($command->dbCmd) {
    case 'update':
      if (array_key_exists('relation', $command) && array_key_exists('isFlipped', $command) &&
          array_key_exists('parentAtom', $command) && array_key_exists('childAtom', $command) &&
          array_key_exists('parentOrChild', $command) && array_key_exists('originalAtom', $command))
        editUpdate($command->relation, $command->isFlipped, $command->parentAtom, $command->childAtom
                  ,$command->parentOrChild, $command->originalAtom);
      else 
        error("Command $command->dbCmd is missing parameters");
      break;
    case 'delete':
      if (array_key_exists('relation', $command) && array_key_exists('isFlipped', $command) &&
          array_key_exists('parentAtom', $command) && array_key_exists('childAtom', $command))
        editDelete($command->relation, $command->isFlipped, $command->parentAtom, $command->childAtom);
      else {
        print_r($command);
        error("Command $command->dbCmd is missing parameters");
      }
      break;
    default:
      error("Unknown command '$command->dbCmd'");
  }
}

function editUpdate($rel, $isFlipped, $parentAtom, $childAtom, $parentOrChild, $originalAtom) {
  if ($childAtom=='x') error('Don\'t update to \'x\'!');
  global $dbName;
  global $relationTableInfo;
  global $conceptTableInfo;
  global $tableColumnInfo;
  
  emitLog("editUpdate($rel, ".($isFlipped?'true':'false').", $parentAtom, $childAtom, $parentOrChild, $originalAtom)");
  
  $table = $relationTableInfo[$rel]['table'];
  $srcCol = $relationTableInfo[$rel]['srcCol'];
  $tgtCol = $relationTableInfo[$rel]['tgtCol'];
  $parentCol = $isFlipped ? $tgtCol : $srcCol;
  $childCol =  $isFlipped ? $srcCol : $tgtCol;
  
  $modifiedCol = $parentOrChild == 'parent' ? $parentCol : $childCol;
  $modifiedAtom= $parentOrChild == 'parent' ? $parentAtom : $childAtom;
  $stableCol   = $parentOrChild == 'parent' ? $childCol : $parentCol;
  $stableAtom  = $parentOrChild == 'parent' ? $childAtom: $parentAtom;
  
  $tableEsc = addSlashes($table);
  $modifiedColEsc = addSlashes($modifiedCol);
  $stableColEsc = addSlashes($stableCol);
  $modifiedAtomEsc = addSlashes($modifiedAtom);
  $stableAtomEsc = addSlashes($stableAtom);
  $originalAtomEsc = addSlashes($originalAtom);
  
  if ($tableColumnInfo[$table][$stableCol]['unique']) { // note: this uniqueness is not set as an SQL table attribute
    $query = "UPDATE `$tableEsc` SET `$modifiedColEsc`='$modifiedAtomEsc' WHERE `$stableColEsc`='$stableAtomEsc'";
    emitLog ($query);
    DB_doquer($dbName, $query);
  }
  else /* if ($tableColumnInfo[$table][$modifiedCol]['unique']) { // todo: is this ok? no, we'd also have to delete stableAtom originalAtom and check if modified atom even exists, otherwise we need an insert, not an update.
    $query = "UPDATE `$tableEsc` SET `$stableColEsc`='$stableAtomEsc' WHERE `$modifiedColEsc`='$modifiedAtomEsc'";
    emitLog ($query);
    DB_doquer($dbName, $query);
  }
  else */ {
    $query = "DELETE FROM `$tableEsc` WHERE `$stableColEsc`='$stableAtomEsc' AND `$modifiedColEsc`='$originalAtomEsc';";
    emitLog ($query);
    DB_doquer($dbName, $query);
    $query = "INSERT INTO `$tableEsc` (`$stableColEsc`, `$modifiedColEsc`) VALUES ('$stableAtomEsc', '$modifiedAtomEsc')";
    emitLog ($query);
    DB_doquer($dbName, $query);
  }
  // if the new atom is not in its concept table, we add it
  $childConcept = $isFlipped ? $relationTableInfo[$rel]['srcConcept'] : $relationTableInfo[$rel]['tgtConcept'];
  $parentConcept =  $isFlipped ? $relationTableInfo[$rel]['tgtConcept'] : $relationTableInfo[$rel]['srcConcept'];
  $modifiedConcept = $parentOrChild == 'parent' ? $parentConcept : $childConcept;
  
  $conceptTable = $conceptTableInfo[$modifiedConcept]['table'];
  $conceptCol = $conceptTableInfo[$modifiedConcept]['col'];
  
  $conceptTableEsc = addSlashes($conceptTable);
  $conceptColEsc = addSlashes($conceptCol);
  
  //emitLog("Checking existence of $childAtom : $childConcept in table $conceptTable, column $conceptCol";)
  $allConceptAtoms = firstCol(DB_doquer($dbName, "SELECT `$conceptColEsc` FROM `$conceptTableEsc`"));
  if (!in_array($modifiedAtom, $allConceptAtoms)) {
    //emitLog( 'not present');
    DB_doquer($dbName, "INSERT INTO `$conceptTableEsc` (`$conceptColEsc`) VALUES ('$modifiedAtomEsc')");
  } else {
    // emitLog('already present');
  }
}


// TODO use backquote for table names? 
// TODO check escaping for table names
function editDelete($rel, $isFlipped, $parentAtom, $childAtom) {
  if ($childAtom=='Pino') emitAmpersandErr('Don\'t delete Pino!');
  global $dbName; 
  global $relationTableInfo;
  emitLog ("editDelete($rel, ".($isFlipped?'true':'false').", $parentAtom, $childAtom)");
  $srcAtom = $isFlipped ? $childAtom : $parentAtom;
  $tgtAtom = $isFlipped ? $parentAtom : $childAtom;
  
  $table = $relationTableInfo[$rel]['table'];
  $srcCol = $relationTableInfo[$rel]['srcCol'];
  $tgtCol = $relationTableInfo[$rel]['tgtCol'];
  
  $tableEsc = addSlashes($table);
  $srcAtomEsc = addSlashes($srcAtom);
  $tgtAtomEsc = addSlashes($tgtAtom);
  $query = "DELETE FROM `$tableEsc` WHERE `$srcCol`='$srcAtomEsc' AND `$tgtCol`='$tgtAtomEsc';";
  emitLog ($query);
  DB_doquer($dbName, $query);
}

function checkRules() {
  global $rulesSql;
  
  $allRulesHold = true;
  
  foreach ($rulesSql as $ruleSql) {
    $rows = DB_doquer($dbName, $ruleSql['sql']);
    if (count($rows) > 0) {
      emitAmpersandErr("Rule '$ruleSql[name]' broken: $ruleSql[meaning]");
      $allRulesHold = false;
    }
    else
      emitLog('Rule '.$ruleSql['name'].' holds');
  } 
  return $allRulesHold;
}



function emitAmpersandErr($err) {
  echo "<div class=AmpersandErr>$err</div>";
}

function emitLog($msg) {
  echo "<div class=LogMsg>$msg</div>";
}

function error($msg) {
  die("<div class=Error>Error in Database.php: $msg</div>");
} // because of this die, the top-level div is not closed, but that's better than continuing in an erroneous situtation

?>