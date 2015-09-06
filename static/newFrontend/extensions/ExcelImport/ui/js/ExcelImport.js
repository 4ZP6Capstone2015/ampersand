var app = angular.module('AmpersandApp');
app.requires[app.requires.length] = 'angularFileUpload'; // add ur.file module to dependencies

AmpersandApp.config(function($routeProvider) {
	$routeProvider
		// default start page
		.when('/ext/ExcelImport',
			{	controller: 'ExcelImportController'
			,	templateUrl: 'extensions/ExcelImport/ui/views/ExcelImport.html'
			,	interfaceLabel: 'Excel import'
			});
});

AmpersandApp.controller('ExcelImportController', function ($scope, $rootScope, FileUploader) {
	
	// $rootScope, so that all information and uploaded files are kept while browsing in the application
	if (typeof $rootScope.uploader == 'undefined') {

		$rootScope.uploader = new FileUploader({
			 url: 'extensions/ExcelImport/api/import'
		});
	}
	
	$rootScope.uploader.onSuccessItem = function(fileItem, response, status, headers) {
		$rootScope.updateNotifications(response.notifications);
        // console.info('onSuccessItem', fileItem, response, status, headers);
    };
    
    $rootScope.uploader.onErrorItem = function(item, response, status, headers){
    	$rootScope.notifications.errors.push( {'message' : response.error.code + ' ' + response.error.message} );	
    	
    };
    
});