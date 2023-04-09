--Group Members:
--Alana Thompson
--Kayvia Harriott
--Jordan Earle

module vehicle_tracking_system

open util/relation 
open util/ternary
open util/ordering[Location] as ord

sig Vehicle{
	tracker: TrackingDevice,
	engine: Engine
}

sig Engine{
	var status: Status
}

sig TrackingDevice{
	var status: Status,
	communicationType: CellTower -> Communication -> SignalStrength,
	connection: Location -> OtherDevice, 
	geofences: Location -> Location, --fact where each location has only 4 location
	var activeLocation: seq Location,
	experience: one Experience,
	var alertType: Alert
}

abstract sig Alert{}
one sig Entered, Exited extends Alert {}

sig Map{
	boundary : Location -> Location
}

sig OtherDevice{
	range: Location -> TrackingDevice,
	communicationType: Communication -> CellTower,
	var permissions: Status
}

sig CellTower{
	originalCommunication: Communication,
	location: Location
}

abstract sig Communication{}
one sig None, EDGE, Com_3G, Com_4G, LTE extends Communication{} 

abstract sig Status{}
one sig On, Off extends Status {}

abstract sig SignalStrength{}
one sig Level_0, Level_1, Level_2, Level_3, Level_4 extends SignalStrength{}

abstract sig Weather {}
one sig SuitableWeather, BadWeather, UnsuitableWeather extends Weather {}

abstract sig Location {
	var weather: Weather
}
	
abstract sig Experience {}
one sig Excellent, Good, Okay, Poor extends Experience {}

pred sanityCheck[
]{
	some Vehicle
	some Engine
	some TrackingDevice
	some CellTower
	some Location
	some Vehicle.tracker
	--some Vehicle.tracker.status == Off
	--one t: TrackingDevice | t.status = Off
	--some t: TrackingDevice |
	--	t.weather = BadWeather 
	--	&& ran[t.communicationType].originalCommunication = LTE --> com 3g

} run sanityCheck for 7 expect 1

/**Constraints/Invariants(?)**/
//The permission of the OtherDevice determines if it's connected to a TrackingDevice
fact PermissionsOtherDevice{
	all o: OtherDevice | o.permissions = Off implies o not in ran[TrackingDevice.connection]
}

//TrackingDevice's geofence can have up to 4 points
fact EachGeofenceUnique{
	all t: TrackingDevice | #ran[t.geofences] = 4
}
// Location1, Location2, Location3, Location4
// alert=Exited

fact InGeofence{ 
	all t1: TrackingDevice | one t1.activeLocation implies t1.alertType = Entered
}


//English - Every vehicle has a unique engine
fact EachVehicleUniqueEngine{
	all disj v1, v2: Vehicle | v1.engine != v2.engine
}

//English - Each tracking device must have a unique vehicle
fact EachTrackingDeviceMustHaveAUniqueVehicle{
	all disj v1, v2: Vehicle | v1.tracker != v2.tracker
}

//English - Each tracking device must be linked to a vehicle
fact EachTrackingDeviceLinkedToAVehicle{
	all t1: TrackingDevice | t1 in Vehicle.tracker
}

//English - All tracking devices must have a communicationType to a cell tower
fact AllTrackingDeviceHaveCommunicationType{
	all t1: TrackingDevice | one t1.communicationType
}

//English - All tracking devices must have one range to a cell tower
fact AllTrackingDeviceHaveOneRange{
	--need to modify how we target the range
	--all t1: TrackingDevice | one t1.range
}

//English - If a tracking device is off then it should not have a communication
//type to the cell tower
fact NoCommunicationTypeIfTrackingDeviceOff {
	--all t1: TrackingDevice |  t1.status = Off implies no t1.communicationType
	all t1: TrackingDevice | t1.status = Off implies ran[t1.communicationType.univ] = None 

}

//English - If a vehicle engine status is off, so is tracking device
fact NoCommunicationTypeIfTrackingDeviceOff {
	all t1: TrackingDevice, veh: Vehicle |  veh.engine.status = Off implies t1.status = Off

}

//English - a recent geofence triggers an alert
fact AlertIfRecentGeofence{
	--all t1: TrackingDevice | some t1.recentGeofence implies one t1.alert
}

fact AlertIfRecentGeofence{ 
	all t1: TrackingDevice | one t1.activeLocation' implies t1.alertType = Exited -- made changes
}

  
//English - A tracking device must only communicate with the cell tower in a specific
//type of communication based on its location to the cell tower i.e. Best - 4G and LTE,
//Acceptable - 3G, 4G, and LTE, Low - 3G and Edge and Out_Of_Range - None
--EDGE, LTE, 3G, 4G
fact CommunicationRelationToLocationOutOfRange { 
	all t: TrackingDevice | ran[t.communicationType] = Level_0 implies ran[t.communicationType.univ] = None and t.experience = Poor
	all t: TrackingDevice | ran[t.communicationType.univ] = None implies ran[t.communicationType] = Level_0
	all t: TrackingDevice | ran[t.communicationType] = Level_1 implies t.experience = Poor

	all t: TrackingDevice | ran[t.communicationType] = Level_2 and ran[t.communicationType.univ] = EDGE implies t.experience = Poor
	all t: TrackingDevice | ran[t.communicationType] = Level_2 and ran[t.communicationType.univ] = Com_3G implies t.experience = Okay
	all t: TrackingDevice | ran[t.communicationType] = Level_2 and ran[t.communicationType.univ] = Com_4G implies t.experience = Okay
	all t: TrackingDevice | ran[t.communicationType] = Level_2 and ran[t.communicationType.univ] = LTE implies t.experience = Okay

	all t: TrackingDevice | ran[t.communicationType] = Level_3 and ran[t.communicationType.univ] = EDGE implies t.experience = Okay
	all t: TrackingDevice | ran[t.communicationType] = Level_3 and ran[t.communicationType.univ] = Com_3G implies t.experience = Good
	all t: TrackingDevice | ran[t.communicationType] = Level_3 and ran[t.communicationType.univ] = Com_4G implies t.experience = Good
	all t: TrackingDevice | ran[t.communicationType] = Level_3 and ran[t.communicationType.univ] = LTE implies t.experience = Excellent

	all t: TrackingDevice | ran[t.communicationType] = Level_4 and ran[t.communicationType.univ] = EDGE implies t.experience = Okay
	all t: TrackingDevice | ran[t.communicationType] = Level_4 and ran[t.communicationType.univ] = Com_3G implies t.experience = Good
	all t: TrackingDevice | ran[t.communicationType] = Level_4 and ran[t.communicationType.univ] = Com_4G implies t.experience = Excellent
	all t: TrackingDevice | ran[t.communicationType] = Level_4 and ran[t.communicationType.univ] = LTE implies t.experience = Excellent
}

//English - The tracking device may only communicate with a 'other device' if 
//the tracking device is Out_Of_Range to a cell tower.
fact OnlyCommunicateWithOtherDeviceWhenOutofRange{ --changed due to updated code
	all t1: TrackingDevice, oth: OtherDevice, loc: Location, cell: CellTower |
		loc -> oth in t1.connection 
			--implies None -> cell = t1.communicationType
			implies cell -> None = t1.communicationType.univ						    
}
--communicationType: CellTower -> Communication -> SignalStrength

fact AutomaticallyCommunicateWithOtherDevice{
	--all t1: TrackingDevice, loc: Location, oth: OtherDevice |
		--(dom[t1.range] = Level_0 && dom[t1.communicationType] = None)
			--	implies loc -> oth in t1.connection	
	--all t1: TrackingDevice-- | --, loc: Location, othD: OtherDevice 
		--| Location -> OtherDevice in t1.connection
	--all t1: TrackingDevice | dom[t1.range] = Level_0 implies one t1.connection
	--need to modify how we target range
all t1: TrackingDevice |  ran[t1.communicationType] = Level_0 implies #t1.connection > 0
}
//
//fact WeatherAffectingCommunication{
//	all t1: TrackingDevice |
//		(dom[t1.communicationType] = EDGE && t1.weather = BadWeather)
//			=> (dom[t1.communicationType] = None)
//	all t1: TrackingDevice |
//		(dom[t1.communicationType] = Com_3G && t1.weather = BadWeather)
//			=> (dom[t1.communicationType] = EDGE)
//	all t1: TrackingDevice |
//		(dom[t1.communicationType] = Com_4G && t1.weather = BadWeather)
//			=> (dom[t1.communicationType] = Com_3G)
//
//	--Badweather + Edge --> becomes None
//	--Badweather + Com_3G --> becomes Edge
//	--Badweather + Com_4G --> becomes 3G
//	--Badweather + LTE --> becomes 4G
//
//	--UnsuitableWeather + Edge --> becomes None
//	--UnsuitableWeather + Com_3G --> becomes None
//	--UnsuitableWeather + Com_4G --> becomes Edge
//	--UnsuitableWeather + LTE --> becomes 3G
//}

fact WeatherAffectingCommunication{
	--need to change to location of tracking device
/*	//Bad weather
	all t: TrackingDevice | (t.weather = BadWeather and dom[t.communicationType.univ].originalCommunication = EDGE) implies ran[t.communicationType.univ]= None
	all t: TrackingDevice |  (t.weather = BadWeather and dom[t.communicationType.univ].originalCommunication = Com_3G) implies ran[t.communicationType.univ] = EDGE
	all t: TrackingDevice |  (t.weather = BadWeather and dom[t.communicationType.univ].originalCommunication = Com_4G) implies ran[t.communicationType.univ] = Com_3G
	all t: TrackingDevice |  (t.weather = BadWeather and dom[t.communicationType.univ].originalCommunication = LTE) implies ran[t.communicationType.univ] = Com_4G

	//Unsuitable weather
	all t: TrackingDevice | (t.weather = UnsuitableWeather and dom[t.communicationType.univ].originalCommunication = EDGE) implies ran[t.communicationType.univ]= None
	all t: TrackingDevice |  (t.weather = UnsuitableWeather and dom[t.communicationType.univ].originalCommunication  = Com_3G) implies ran[t.communicationType.univ] = None
	all t: TrackingDevice |  (t.weather = UnsuitableWeather and dom[t.communicationType.univ].originalCommunication  = Com_4G) implies ran[t.communicationType.univ] = EDGE
	all t: TrackingDevice |  (t.weather = UnsuitableWeather and dom[t.communicationType.univ].originalCommunication  = LTE) implies ran[t.communicationType.univ] = Com_3G
	*/

}



/**/
--Preds Scenarios
/*1
The tracking device is far away from the cell tower which means there are no CommunicationTypes available
and automatically create a connection with another device
*/
pred ScenarioOne[t1: TrackingDevice]{
	ran[t1.communicationType] = Level_0
} run ScenarioOne for 3 expect 1

/*2
Multiple cell towers in a geographic location and at least one tower must be able to identify that
a tracking device is near a cell tower.
*/
pred ScenarioTwo[c: CellTower]{
	--gt[#Vehicle,1]
	gt[#TrackingDevice,1]
	gt[#CellTower,1]
	--some TrackingDevice.communicationType.c 
} run ScenarioTwo for 7 expect 1

/*3
The tracking device is near a cell tower,
but the weather condition is bad resulting in poor or okay experience.
*/
pred ScenarioThree[t: TrackingDevice]{
	--need to modify how we target the range
	//dom[t.range] = Level_3
	--need to change to location of tracking device
	--t.weather = UnsuitableWeather
} run ScenarioThree for 7 expect 1

/*4 - Vehicle has left geofence and should have an alert 
*/
/*
pred ScenarioFour[t: TrackingDevice]{
	--some t.recentGeofence
} run ScenarioFour for 7 expect 1
*/

//Alana change
pred ScenarioFour[t: TrackingDevice]{ --made changes
--	some t.activeGeofence'
} run ScenarioFour for 7 expect 1


/*5 - The tracking device is near a cell tower, outside of it's geofence, 
weather condition is good and the tracking device supports LTE
*/
pred ScenarioFive[t: TrackingDevice]{
	--need to modify how we target the range
	--dom[t.range] = Level_4
	--some t.recentGeofence
	--need to change to location of tracking device
	--t.weather = SuitableWeather

} run ScenarioFive for 7 expect 1


	