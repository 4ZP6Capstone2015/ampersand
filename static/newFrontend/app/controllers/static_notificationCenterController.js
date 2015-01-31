AmpersandApp.controller('static_notificationCenterController', function ($scope, $rootScope, $routeParams, $timeout, Restangular) {
	
	$rootScope.notifications = Restangular.one('notifications/all').get().$object;
	
	$rootScope.updateNotifications = function(notifications){
		$rootScope.notifications = notifications;
		$timeout(function() {
	    	console.log('now.');
	    	$rootScope.notifications.successes = [];
	    }, 3000);
	}
	
	$scope.closeAlert = function(alerts, index) {
		alerts.splice(index, 1);
	}
	
	$rootScope.switchShowViolations = true;
	$rootScope.switchShowInfos = false;
	
	$rootScope.toggleShowViolations = function(){
		$rootScope.switchShowViolations = !$rootScope.switchShowViolations;
	}
	
	$rootScope.toggleShowInfos = function(){
		$rootScope.switchShowInfos = !$rootScope.switchShowInfos;
	}
	
});