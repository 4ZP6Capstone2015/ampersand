<?php

class Concept {

	public static function getAllConcepts(){
		global $conceptTableInfo; // from Generics.php
		
		return array_keys($conceptTableInfo);
	}

	public static function getSpecializations($concept) {
		global $allSpecializations;
		
		return isset($allSpecializations[$concept]) ? $allSpecializations[$concept] : array ();
		
	}
	
	public static function getAllAtomObjects($concept){
		
		foreach (Concept::getAllAtomIds($concept) as $tgtAtomId){
			$tgtAtom = new Atom($tgtAtomId, $concept);
			$arr[] = $tgtAtom;
		}
		return $arr;
	}
	
	public static function getAllAtomIds($concept){
		$database = Database::singleton();
		global $conceptTableInfo;
	
		$conceptTable = $conceptTableInfo[$concept][0]['table']; // $conceptTableInfo[$concept] is an array of tables with arrays of columns maintaining $concept
		$conceptCol = $conceptTableInfo[$concept][0]['cols'][0]; // for lookup, we just take the first table and its first column
		$conceptTableEsc = addslashes($conceptTable);
		$conceptColEsc = addslashes($conceptCol);
	
		return $tgtAtoms = array_column($database->Exe("SELECT DISTINCT `$conceptColEsc` FROM `$conceptTableEsc` WHERE `$conceptColEsc` IS NOT NULL"),$conceptColEsc);
		
	}	
	
	public static function isAtomInConcept($atom, $concept) {
		return in_array( $atom, (array)Concept::getAllAtomIds($concept) );
	}
	
	public static function createNewAtom($concept){
		$time = explode(' ', microTime()); // yields [seconds,microseconds] both in seconds, e.g. ["1322761879", "0.85629400"]
		$atomId = $concept.'_'.$time[1]."_".substr($time[0], 2,6);  // we drop the leading "0." and trailing "00"  from the microseconds  
		
		return $atomId;
	}
	
	public static function getView($concept){
		global $allViews;
		
		foreach ((array)$allViews as $view){
			if ($concept == $view['concept'] || in_array($concept, Concept::getSpecializations($view['concept']))) return $view;
		}
		return null;
	}

}

?>