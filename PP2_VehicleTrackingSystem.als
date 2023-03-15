/*
An Alloy Model that includes:
a. Parts 1c, 1di, and 1dii - put the English description for the invariant 
as a comment with the invariant specification; and
b. at least 5 predicates that give instances of your system - include a 
description for what the predicate is specifying (use instances that show 
important scenarios for your system).
*/
--Group Members:
--Alana Thompson
--Jordan Earle
--Kayvia Harriott
module vehicle_tracking_system
open util/relation 
open util/ternary

sig Vehicle{
	tracker: TrackingDevice,
	battery: lone Battery,
	engine: Engine
}

sig Engine{
	status: Status
}

sig TrackingDevice{
	track_dev_battery: Battery,
	status: Status,
	communicationType: Communication -> CellTower,
	range: Bar -> CellTower,
	connection: Location -> OtherDevice, 
	geofences: Location -> Location,
	activeGeofence: geofences,
	recentGeofence: geofences,
	alert: Alert -> (activeGeofence+recentGeofence),
	experience: one Experience
	//signal_strength: Bar -- feel like I advised moving this to Tracking Device; moved to range
}

abstract sig Alert{}
one sig Entered, Left extends Alert {}


sig OtherDevice{
	range: Location -> TrackingDevice,
	communicationType: Communication -> CellTower
}

sig CellTower{
}

sig Battery{}

abstract sig Communication{}
one sig None, EDGE, Com_3G, Com_4G, LTE extends Communication{} 

abstract sig Status{}
one sig On, Off extends Status {}

abstract sig Bar{}
one sig Level_0, Level_1, Level_2, Level_3, Level_4 extends Bar{}

abstract sig Weather {}
one sig GoodWeather, SuitableWeather, BadWeather, UnsuitableWeather extends Weather {}

abstract sig Location {}

abstract sig Experience {}
one sig Excellent, Good, Poor extends Experience {}

pred sanityCheck[
]{
	// #Vehicle > 3
	// #SimCard > 3
	// #TrackingDevice > 2
	// some Vehicle.tracker
	some Vehicle
	some Engine
	some TrackingDevice
	some CellTower
	some Location
	some Vehicle.tracker
	some v: Vehicle | v.tracker.status = On
	some v: Vehicle | v.tracker.status = Off
	//some range
	//some TrackingDevice.communication
	//some CellTower.communication
	//some OtherDevice.communication

} run sanityCheck for 7 expect 1

/**Constraints/Invariants(?)**/

//English - Every vehicle has a unique engine
fact EachVehicleUniqueEngine{ --edited
	all disj v1, v2: Vehicle | v1.engine != v2.engine
}

//English - Each tracking device must have a unique vehicle
fact EachTrackingDeviceMustHaveAUniqueVehicle{ --edited
	all disj v1, v2: Vehicle | v1.tracker != v2.tracker
}

//English - All cell towers must have a range to tracking devices
//and the relation must only exist once
fact AllCellTowersHaveRangeToTrackingDevice{ --edited
	//all t1: TrackingDevice,  c1: CellTower | some l1: Location
//		|t1.range = l1 -> c1 --giving error, to add back
}

//English - All cell towers must have a communicationType to tracking devices
//and the relation must only exist once
fact AllCellTowersHaveCommunicationTypeToTrackingDevice{
	all t1: TrackingDevice, c1: CellTower | some com: Communication
		| t1.communicationType = com -> c1
}

//English - A tracking device must only communicate with the cell tower in a specific
//type of communication based on its location to the cell tower i.e. Best - 4G and LTE,
//Acceptable - 3G, 4G, and LTE, Low - 3G and Edge and Out_Of_Range - None
--EDGE, LTE, 3G, 4G
fact CommunicationRelationToLocationOutOfRange { --edited
	/*
	all t: TrackingDevice | dom[t.signal_strength] = Level_0 implies no dom[t.communicationType] = None
	all t: TrackingDevice | dom[t.signal_strength] = Level_1 implies no dom[t.communicationType] = EDGE
	all t: TrackingDevice | dom[t.signal_strength] = Level_2 implies no dom[t.communicationType] = Com_3G
	all t: TrackingDevice | dom[t.signal_strength] = Level_3 implies no dom[t.communicationType] = Com_4G
	all t: TrackingDevice | dom[t.signal_strength] = Level_4 implies no dom[t.communicationType] = LTE
	*/
} -- post edit: I don't think that this should be a fact. I believe you can have 4 bars and be on Edge
-- so add an Experience sig that would use the words that Location had
-- gonna think about this fact later

fact CommunicationRelationToWeather {
	
}

//English - Each tracker has a unique battery - good
fact uniqueTrackerBattery{
	all disj t1, t2: TrackingDevice | t1.track_dev_battery != t2.track_dev_battery
}

//English - The tracking device may only communicate with a 'other device' if 
//the tracking device is Out_Of_Range to a cell tower.
fact OnlyCommunicateWithOtherDeviceWhenOutofRange{ --changed due to updated code
	all t1: TrackingDevice, oth: OtherDevice, loc: Location, cell: CellTower |
		loc -> oth in t1.connection 
			implies None -> cell = t1.communicationType
}


/**/
--Preds Scenarios

/*1 - The tracking device is far away from the cell tower, it's communication is 4G,
and the weather condition is good
---- your fact literally says that if the device is out of range 
it does not have a CommunicationType, so this does not make sense
you have not connected weather to anything so not sure how it will affect anything
I am going to specify
-the tracking device is far away from the cell tower -- this should automatically produce no Communtication Type
-- and automatically create a connection with another device
*/
pred ScenarioOne[t1: TrackingDevice]{
	gt[#Vehicle,1] --some Vehicle
	gt[#TrackingDevice,1] --some TrackingDevice
	gt[#CellTower,1] --some CellTower
	
	dom[t1.range] = Level_0
	
} run ScenarioOne for 3 expect 1

/*2 - Multiple cell towers in a geographic location and at least one tower must be able to identify that
a tracking device is near a cell tower
*/
pred ScenarioTwo[c: CellTower]{
	gt[#Vehicle,1]
	gt[#CellTower,1]
	//some communicationType.c --giving error, to add back

} run ScenarioTwo for 7 expect 1

/*3 - The tracking device is near a cell tower, inside the geofence but the weather condition
is bad resulting in poor communication; what does being inside the geofence have to do with connection to tower?
-----again no connection to weather specified
*/
pred ScenarioThree[t: TrackingDevice]{
	dom[t.range] = Level_3
	//t.weather = UnsuitableWeather --giving error, to add back

} run ScenarioThree for 7 expect 1

/*4 - create a new pred cuz this is #1
vehicle has left geofence and should have an alert
add other stuff but this is all we care about
*/
pred ScenarioFour[t: TrackingDevice]{
	some t.recentGeofence

} run ScenarioFour for 7 expect 1


/*5 - The tracking device is near a cell tower, outside of it's geofence, weather condition is good
The tracking device supports LTE
*/
pred ScenarioFive[t: TrackingDevice]{
	dom[t.range] = Level_4
	some t.recentGeofence
	//t.weather = GoodWeather --giving error, to add back

} run ScenarioFive for 7 expect 1


// - Tracking device
// - geofence
// - weather conditions
// - cell towers
// - communication type( 3G, LTE, 4G)