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
	one TrackingDevice
	some towerCommunication
	some towerStrength


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
	all t: TrackingDevice | (no ran[t.towerCommunication] implies ran[t.towerStrength] = Level_0) --unsure if i corrected this properly
		--	and (ran[t.towerStrength] = Level_0 implies ran[t.towerCommunication] = None) --unsure if needed
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
}

//English - 
fact ActiveGeofencePreviousLocationNotLastLocation {
--	all t: TrackingDevice | #t.activeLocation > 1 
	--			implies (prev[t.activeLocation] != last[t.activeLocation])
	--go through and check if it has a next and the next is not equal to the current

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

//English - Each tracking device can only have one tower strength to a cell tower
fact OneTowerStrengthTrackingDevice{
	all t: TrackingDevice | some t.towerCommunication implies one t.towerStrength
}

//English - The CellTower in towerCommunication and towerStrength must be the same
fact SameCellTowerInTrackingDevice{
	all t: TrackingDevice, c: CellTower | c in dom[t.towerCommunication] implies c in dom[t.towerStrength]
}

//English - Each geofence of a tracking device must have at most 4 Locations
fact GeofenceDefinition{
	--unsure if this works
	--all t: TrackingDevice | #t.geofences = 4
}

/**Scenarios**/

/*1 - The tracking device is far away from the cell tower which means there are no CommunicationTypes available
and automatically create a connection with another device */
pred ScenarioOne[t1: TrackingDevice]{
	ran[t1.towerStrength] = Level_0
} run ScenarioOne for 7 expect 1

/*2 - Multiple cell towers in a geographic location and at least one tower must be able to identify that
a tracking device is able to have a connection to a cell tower. */
pred ScenarioTwo[c: CellTower]{
	some TrackingDevice
	gt[#CellTower,1]
} run ScenarioTwo for 7 expect 1

/*3 - The tracking device is near a cell tower,
but the weather condition is bad resulting in poor or okay experience. */
pred ScenarioThree[t: TrackingDevice]{
	ran[t.towerStrength] = Level_3 
			or  ran[t.towerStrength] = Level_4
	last[t.activeLocation].weather = UnsuitableWeather
} run ScenarioThree for 7 expect 1

/*4 - Vehicle has left geofence and should have an alert */
pred ScenarioFour[t: TrackingDevice]{
	last[t.activeLocation] not in ran[t.geofences]
} run ScenarioFour for 7 expect 1

/*5 - The tracking device is near a cell tower, outside of it's geofence, 
weather condition is suitable and the tracking device supports LTE
*/
pred ScenarioFive[t: TrackingDevice]{
	ran[t.towerStrength] = Level_4
	last[t.activeLocation] not in ran[t.geofences]
	last[t.activeLocation].weather = SuitableWeather
	let cell = dom[t.towerCommunication] {
		cell.location.weather = SuitableWeather
	}
	
} run ScenarioFive for 7 expect 1

//English - One a tracking device leaves it's geofence,
//it sends the alert 'Outside'
pred leaveGeofence[t: TrackingDevice, l: Location] {
	//preconditions
	some t.activeLocation
	some l & (dom[Map.map] + ran[Map.map])
	l not in ran[t.geofences]
	t.alertType = Inside

	//post conditions
	--last[t'.activeLocation] = l
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

//English - A function that takes a tracking device, cell tower and location,
//the location is the new location of the tracking device which is outside the range of
//the cell tower
pred LeaveRangeOfCellTower[track: TrackingDevice, cell: CellTower, loc: Location]{
	//preconditions
	track.status = On --tracking device status is on
	ran[track.towerStrength] != Level_0 --signal strength has to be not equal to Level_0
	ran[track.towerCommunication] != None --communication is not equal to None
	some track.towerCommunication && dom[track.towerCommunication] = cell --tracking device and cell tower has connection
	some track.towerStrength && dom[track.towerStrength] = cell --shouldn't have a connection to a OtherDevice
	--last[track.activeLocation] != loc --last activeLocation isn't the new one being added
	lastLocation != loc --last activeLocation isn't the new one being added
	--^^ i think this works, but to ask Monique the difference
	--active location should only be + 1
	some v: Vehicle | track in v.tracker implies v.engine.status = On --engine status stays on

	//postconditions
	last[track'.activeLocation'] = loc -- location has changed
	ran[track'.towerStrength'] = Level_0 --the towerStrength is now Level_0
	ran[track'.towerCommunication'] = None --the towerCommunication is now None

	//framecondition --for all vars
	cell in dom[track.towerCommunication] && cell in dom[track'.towerCommunication'] --cell tower doesn't change
	cell in dom[track.towerStrength] && cell in dom[track'.towerStrength'] --cell tower doesn't change
	track.alertType' = track.alertType --alert type doesn't change
	some v: Vehicle | track in v.tracker implies v'.engine'.status' = On --engine status stays the same
	track.status = track'.status' -- status doesn't change
	track.towerCommunication != track'.towerCommunication' -- towerCommunication changes
	track.towerStrength != track'.towerStrength' -- towerStrength changes
	track.activeLocation != track'.activeLocation' -- activeLocation changes
	cell.location != loc --the cell tower is not in the new out-of-range location
} run LeaveRangeOfCellTower for 7 expect 1

//English - A function that changes the weather in a location
pred ChangeWeatherOfLocation[loc: Location, we: Weather]{
	//Preconditions	
	loc.weather != we --the weather of the location isn't the new weather
	

	//Postconditions
	loc'.weather' = we --location has changed


	//Frameconditions


} run ChangeWeatherOfLocation for 7 expect 1


//English - A function that changes the weather in a location
pred ChangeStatusOfDevice[dev: TrackingDevice, stat: Status]{
	//Preconditions	
	--status is not the new status
	

	//Postconditions
	--status is the new status
	



	//Frameconditions
	


} run ChangeWeatherOfLocation for 7 expect 1

--test function
//English - A function that changes the alert of a tracking device when leaving
//a geofence
pred AlertWithGeofence[track: TrackingDevice, loc: Location, alert: Alert]{
//	--leaving
//	all t1: TrackingDevice | last[t1.activeLocation] not in ran[t1.geofences] 
//			implies t1.alertType = Outside
//	all t1: TrackingDevice | t1.alertType = Outside 
//			implies last[t1.activeLocation] not in ran[t1.geofences]
//
//	//entering
//	all t1: TrackingDevice | last[t1.activeLocation] in ran[t1.geofences] 
//		implies t1.alertType = Inside
//	all t1: TrackingDevice | t1.alertType = Inside 
//		implies last[t1.activeLocation] in ran[t1.geofences]


	--leaving
	track.alertType = Inside && alert = Outside implies{
		//Preconditions
		last[track.activeLocation] != loc --the trackingdevice's last location must be inside the geofence
		loc not in ran[track.geofences] --the new location is not in the trackingDevice's geofences	

		//Postconditions
		last[track'.activeLocation'] = loc --the trackingdevice's last location has changed
		track'.alertType' = alert --the tracking device's alert has changed

		//Frameconditiond
		track.geofences = track'.geofences' --geofences doesn't change
	
	}

	--entering
	track.alertType = Outside && alert = Inside implies {
		//Preconditions
		last[track.activeLocation] != loc --the trackingdevice's last location must be inside the geofence
		loc in ran[track.geofences] --the new location is not in the trackingDevice's geofences	

		//Postconditions
		track'.activeLocation' != track.activeLocation -- i think this should be added to 
		--last[track'.activeLocation'] = loc --the trackingdevice's last location has changed
		--the new location is in the trackingDevice's geofence

		track'.alertType' = alert --the tracking device's alert has changed

	}

	//Frameconditions
	track.alertType != alert
	track.geofences = track'.geofences'
	track.alertType != track'.alertType'



} run AlertWithGeofence for 7 expect 1

pred ChangeAlert[track: TrackingDevice, alert: Alert]{

} run ChangeAlert for 7 expect 1

/**Functions**/
fun lastLocation: Location { last[TrackingDevice.activeLocation] }


/**Asserts & Checks**/
//English - all tracking devices are properly set up
assert ValidTrackingDevices{
	no t: TrackingDevice | t not in Vehicle.tracker

} check ValidTrackingDevices for 7 expect 0

//English - No TrackingDevice should be able to communicate
//with a OtherDevice if the OtherDevice's permissions are off 
assert OtherDevicePermissionsOff{
	no o: OtherDevice | o.permissions = Off && o in ran[TrackingDevice.connection]
} check OtherDevicePermissionsOff for 7 expect 0







