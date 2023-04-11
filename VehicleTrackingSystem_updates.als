--Group Members:
--Alana Thompson
--Kayvia Harriott
--Jordan Earle

module vehicle_tracking_system

open util/relation 
open util/ternary
open util/graph[Location]

sig Vehicle{
	tracker: TrackingDevice,
	engine: Engine
}

sig Engine{
	var status: Status
}

sig TrackingDevice{
	var status: Status,
	var towerCommunication: CellTower -> Communication,
	var towerStrength: CellTower -> SignalStrength,
	connection: Location -> OtherDevice, 
	geofences: Location -> Location, --fact where each location has only 4 location
	var activeLocation: seq Location,
	experience: one Experience,
	var alertType: Alert
}

abstract sig Alert{}
one sig Inside, Outside extends Alert {} -- inside means it has entered and is also within  geofence, opposite can be assumed for outside

one sig Map{
	map: Location -> Location
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

sig Location {
	var weather: Weather
}
	
abstract sig Experience {}
one sig Excellent, Good, Okay, Poor extends Experience {}

fact {
	some Map.map
	gt[#Location,4]
}

pred sanityCheck[
]{
	#TrackingDevice > 1
--	#Location = 4
	--some TrackingDevice.communicationType

} run sanityCheck for 7 expect 1


/**Facts**/

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
	--may need to modify, do we mean it can only be connected to one cell tower?
	-- prob not, so maybe one type of communication to a cell tower
	all t1: TrackingDevice | one t1.towerCommunication
}

//The permission of the OtherDevice determines if it's connected to a TrackingDevice
fact PermissionsOtherDevice{
	all o: OtherDevice | o.permissions = Off implies o not in ran[TrackingDevice.connection]
}

//English - a geofence is a cycle with 4 locations
fact GeofenceIsCycleWith4Locations{
	all t1: TrackingDevice | #ran[t1.geofences] = 4
	all t1: TrackingDevice| dom[t1.geofences] = ran[t1.geofences] and eq[#t1.geofences,4]
	all t: TrackingDevice, l: dom[t.geofences] | l->l not in t.geofences
	all t: TrackingDevice, l1, l2: dom[t.geofences] | l1->l2 in t.geofences implies l2->l1 not in t.geofences
}
//English - geofence is in map
fact GeofenceIsinMap{
	all t1: TrackingDevice | t1.geofences in Map.map
}

//English - if there is an alert, the device must be somewhere
fact AlertMustHaveReason{
	all t: TrackingDevice | some t.alertType implies some t.activeLocation
}

//English - 
fact AlertIfInsideGeofence{ 
	all t1: TrackingDevice | last[t1.activeLocation] in ran[t1.geofences] implies t1.alertType = Inside -- made changes
	all t1: TrackingDevice | t1.alertType = Inside implies last[t1.activeLocation] in ran[t1.geofences]
}

//English - 
fact AlertIfOutsideGeofence{ 
	all t1: TrackingDevice | last[t1.activeLocation] not in ran[t1.geofences] implies t1.alertType = Outside -- made changes
	all t1: TrackingDevice | t1.alertType = Outside implies last[t1.activeLocation] not in ran[t1.geofences]
}

//English - If a tracking device is off then it should not have a communication
//type to the cell tower
fact NoCommunicationTypeIfTrackingDeviceOff {
	all t1: TrackingDevice | t1.status = Off implies ran[t1.towerCommunication] = None 
}

//English - If a vehicle engine status is off, so is tracking device
fact NoCommunicationTypeIfTrackingDeviceOff {
	all t1: TrackingDevice, veh: Vehicle |  veh.engine.status = Off implies t1.status = Off
}
//if a location is inside the geofence
-- Geo A B C D, E F G H

//English - If a vehicle engine status is off, so is tracking device
fact VehicleEngineStatusOffTrackingDeviceOff {
	all t1: TrackingDevice, veh: Vehicle |  veh.engine.status = Off implies t1.status = Off
}

//English - A tracking device must only communicate with the cell tower in a specific
//type of communication based on its location to the cell tower i.e. Best - 4G and LTE,
//Acceptable - 3G, 4G, and LTE, Low - 3G and Edge and Out_Of_Range - None
--EDGE, LTE, 3G, 4G
fact CommunicationRelationToLocationOutOfRange { 
	all t: TrackingDevice | ran[t.towerStrength] = Level_0 implies ran[t.towerCommunication] = None and t.experience = Poor
	--wee need to edit this, forgot what it means--all t: TrackingDevice | no ran[t.communicationType] implies ran[t.communicationType] = Level_0
	all t: TrackingDevice | ran[t.towerStrength] = Level_1 implies t.experience = Poor

	all t: TrackingDevice | ran[t.towerStrength] = Level_2 and ran[t.towerCommunication] = EDGE implies t.experience = Poor
	all t: TrackingDevice | ran[t.towerStrength] = Level_2 and ran[t.towerCommunication] = Com_3G implies t.experience = Okay
	all t: TrackingDevice | ran[t.towerStrength] = Level_2 and ran[t.towerCommunication] = Com_4G implies t.experience = Okay
	all t: TrackingDevice | ran[t.towerStrength] = Level_2 and ran[t.towerCommunication] = LTE implies t.experience = Okay

	all t: TrackingDevice | ran[t.towerStrength] = Level_3 and ran[t.towerCommunication] = EDGE implies t.experience = Okay
	all t: TrackingDevice | ran[t.towerStrength] = Level_3 and ran[t.towerCommunication] = Com_3G implies t.experience = Good
	all t: TrackingDevice | ran[t.towerStrength] = Level_3 and ran[t.towerCommunication] = Com_4G implies t.experience = Good
	all t: TrackingDevice | ran[t.towerStrength] = Level_3 and ran[t.towerCommunication] = LTE implies t.experience = Excellent

	all t: TrackingDevice | ran[t.towerStrength] = Level_4 and ran[t.towerCommunication] = EDGE implies t.experience = Okay
	all t: TrackingDevice | ran[t.towerStrength] = Level_4 and ran[t.towerCommunication] = Com_3G implies t.experience = Good
	all t: TrackingDevice | ran[t.towerStrength] = Level_4 and ran[t.towerCommunication] = Com_4G implies t.experience = Excellent
	all t: TrackingDevice | ran[t.towerStrength] = Level_4 and ran[t.towerCommunication] = LTE implies t.experience = Excellent
}

//English - The tracking device may only communicate with a 'other device' if 
//the tracking device is Out_Of_Range to a cell tower.
fact OnlyCommunicateWithOtherDeviceWhenOutofRange{ --changed due to updated code
	all t1: TrackingDevice, oth: OtherDevice, loc: Location, cell: CellTower |
		loc -> oth in t1.connection 
			implies cell -> None = t1.towerCommunication						    
}

fact AutomaticallyCommunicateWithOtherDevice{
	all t1: TrackingDevice |  ran[t1.towerStrength] = Level_0 implies #t1.connection > 0
}

fact WeatherAffectingCommunication{
	--need to change to location of tracking device
	//Bad weather
	all t: TrackingDevice |  (last[t.activeLocation].weather = BadWeather and dom[t.towerCommunication].originalCommunication = EDGE) implies ran[t.towerCommunication]= None
	all t: TrackingDevice |  (last[t.activeLocation].weather = BadWeather and dom[t.towerCommunication].originalCommunication = Com_3G) implies ran[t.towerCommunication] = EDGE
	all t: TrackingDevice |  (last[t.activeLocation].weather = BadWeather and dom[t.towerCommunication].originalCommunication = Com_4G) implies ran[t.towerCommunication] = Com_3G
	all t: TrackingDevice |  (last[t.activeLocation].weather= BadWeather and dom[t.towerCommunication].originalCommunication = LTE) implies ran[t.towerCommunication] = Com_4G

	//Unsuitable weather
	all t: TrackingDevice |  (last[t.activeLocation].weather = UnsuitableWeather and dom[t.towerCommunication].originalCommunication = EDGE) implies ran[t.towerCommunication]= None
	all t: TrackingDevice |  (last[t.activeLocation].weather = UnsuitableWeather and dom[t.towerCommunication].originalCommunication  = Com_3G) implies ran[t.towerCommunication] = None
	all t: TrackingDevice |  (last[t.activeLocation].weather= UnsuitableWeather and dom[t.towerCommunication].originalCommunication  = Com_4G) implies ran[t.towerCommunication] = EDGE
	all t: TrackingDevice |  (last[t.activeLocation].weather = UnsuitableWeather and dom[t.towerCommunication].originalCommunication  = LTE) implies ran[t.towerCommunication] = Com_3G
	
}

//Additional Facts
//All locations in a geofence have the same weather
fact GeofenceLocationSameWeather{
	all t:TrackingDevice | #dom[t.geofences].weather = 1  
					//and #dom[t.geofences].weather = 1 
}

//English - 
fact GeofencePreviousLocationNotLastLocation {
--	all t: TrackingDevice | #t.activeLocation > 1 
	--			implies (prev[t.activeLocation] != last[t.activeLocation])
	--go through and check if it has a next and the next is not equal to the current
}

//English - 
fact ActiveGeofencePreviousLocationNotLastLocation {
	--for testing
	//#TrackingDevice.activeLocation = 4
	--all t: TrackingDevice | #t.activeLocation > 1 
			--	implies (prev[t.activeLocation] != last[t.activeLocation])
	--go through and check if it has a next and the next is not equal to the current
	--no duplicates activeLocation.Location
	--all i: Int, t: TrackingDevice | i < #activeLocation - 1 
				--=> t.activeLocation[i] != t.activeLocation[i+1]
	--all t: TrackingDevice | last[t.activeLocation] = first[t.activeLocation]
	
	--all i: Int, t: TrackingDevice | (i < #t.activeLocation - 1)
			--					implies t.activeLocation[i] != t.activeLocation[i-1]
}


/**/
--Preds Scenarios
/*1
The tracking device is far away from the cell tower which means there are no CommunicationTypes available
and automatically create a connection with another device
*/
pred ScenarioOne[t1: TrackingDevice]{
	ran[t1.towerStrength] = Level_0
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

pred leaveGeofence[t: TrackingDevice, l: Location] {
	//preconditions
	some t.activeLocation
	some l & (dom[Map.map] + ran[Map.map])
	l not in ran[t.geofences]
	t.alertType = Inside

	//post conditions
--	last[t'.activeLocation] = l
	t'.alertType = Outside

	//frameconditions - todo

} run leaveGeofence for 7 expect 1

	
//English - Disconnecting a OtherDevice from a connected TrackingDevice if the OtherDevice's
//permissions changes from On to Off
pred DisconnectFromTrackingDevicePermissionsChange[other: OtherDevice, track: TrackingDevice]{
	//preconditions
	other.permissions = On
	other in ran[track.connection]
	track.status = On
	ran[track.towerCommunication] = None
	ran[track.towerStrength] = Level_0


	//postconditions
	other'.permissions' = Off
	other not in ran[track'.connection']
	no other.range
	ran[track.towerCommunication] != None --added
	

	//frame
	track' = track
	other' = other
	other.communicationType = other'.communicationType'

} run DisconnectFromTrackingDevicePermissionsChange for 7 expect 1

pred LeaveRangeOfCellTower[track: TrackingDevice, cell: CellTower, loc: Location]{
	-- tracking device leaving the range of cell tower
	//precondition
	--tracking device and cell tower has connection
	--signal strength has to be not equal to Level_0
	ran[track.towerStrength] != Level_0
	--status of tracking device has to be on
	track.status = On
	--communication is not equal to None
	ran[track.towerCommunication] != None
	--connection - shouldn't be connected to other device
	

	//postcondition
	-- a new location is added
	
	//framecondition
	-- cell tower remains the same
	cell' = cell
	--alerttype doesn't change 
	track.alertType' = track.alertType

} run LeaveRangeOfCellTower for 7 expect 1

















