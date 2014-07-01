<?php

/* FUNCTIONS OF NEWER VERSIONS OF PHP */
require_once (__DIR__ . '/functions/array_column.php');

/* OTHER GENERIC FUNCTIONS */
require_once (__DIR__ . '/functions/getDirectoryList.php');

/* INCLUDES OF AMPERSAND FRAMEWORK */

require_once (__DIR__ . '/../ampersand/Generics.php'); // loading the Ampersand model

require_once (__DIR__ . '/../db/Database.php');

require_once (__DIR__ . '/Concept.php');
require_once (__DIR__ . '/ErrorHandling.php');
require_once (__DIR__ . '/Relation.php');
require_once (__DIR__ . '/Role.php');
require_once (__DIR__ . '/RuleEngine.php');
require_once (__DIR__ . '/Session.php');
require_once (__DIR__ . '/UserInterface.php');
require_once (__DIR__ . '/Viewer.php');

require_once (__DIR__ . '/../localSettings.php');

?>