<?php

class Config {
	
	public static function get($configVar, $scope = 'global'){
		if (!isset($GLOBALS[$scope][$configVar])) throw new Exception("Variable $configVar in scope $scope does not exists", 500);
		
		return $GLOBALS[$scope][$configVar];
	}
	
	public static function set($configVar, $scope, $value){
		$GLOBALS[$scope][$configVar] = $value;
		
		return true;
	}
}

// Default configuration
Config::set('contextName', 'global', $contextName); // from Generics.php
Config::set('sessionExpirationTime', 'global', 60*60); // expiration time in seconds
Config::set('productionEnv', 'global', false); // set environment as production deployment (or not = default)

// Default CRUD rights for interfaces
Config::set('defaultCrudC', 'global', true);
Config::set('defaultCrudR', 'global', true);
Config::set('defaultCrudU', 'global', true);
Config::set('defaultCrudD', 'global', true);

?>