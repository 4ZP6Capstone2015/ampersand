<?php

use Luracast\Restler\Data\Object;
use Luracast\Restler\RestException;

class ExcelImportApi{
	
	/****************************** PARSE FILE ******************************/
	/**
	 * @url POST import
	 */
	public function post(){
		try{
			$session = Session::singleton();
			
			// Check sessionRoles if allowedRolesForExcelImport is specified
			$allowedRoles = Config::get('allowedRolesForExcelImport','excelImport');
			if(!is_null($allowedRoles)){
				$ok = false;
			
				foreach($session->getSessionRoles() as $role){
					if(in_array($role->label, $allowedRoles)) $ok = true;
				}
				if(!$ok) throw new Exception("You do not have access to import excel files", 401);
			}
			
			if (is_uploaded_file($_FILES['file']['tmp_name'])){
				// Parse:
				$parser = new ImportExcel($_FILES['file']['tmp_name']);
				$result = $parser->ParseFile();
				unlink($_FILES['file']['tmp_name']);
			}else{
			    Notifications::addError('No file uploaded');
			}
			
			$result = array('notifications' => $result, 'files' => $_FILES);
			return $result;
			
		}catch(Exception $e){
			throw new RestException($e->getCode(), $e->getMessage());
		}
	}
}
?>