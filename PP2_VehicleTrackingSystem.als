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
	range: Location -> CellTower,
	connection: Location -> OtherDevice, 
	geofences: Location -> Location,
	activeGeofence: geofences,
	recentGeofence: geofences,
	alert: Alert -> (activeGeofence+recentGeofence)
}

abstract sig Alert{}
one sig Entered, Left extends Alert {}


sig OtherDevice{
	range: Location -> TrackingDevice,
	communicationType: Communication -> CellTower
}

sig CellTower{
	signal_strength: Bar
}

sig Battery{}

abstract sig Communication{}
one sig None, EDGE, Com_3G, Com_4G, LTE extends Communication{} 

abstract sig Status{}
one sig On, Off extends Status {}

abstract sig Bar{}
one sig Level_1, Level_2, Level_3, Level_4 extends Bar{}

abstract sig Weather {}
one sig GoodWeather, SuitableWeather, BadWeather, UnsuitableWeather extends Weather {}

abstract sig Location {}
one sig Best, Acceptable, Low, Out_Of_Range extends Location {}

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
fact EachVehicleUniqueEngine{
	all disj v1, v2: Vehicle | v1 != v2 implies v1.engine != v2.engine
}

//English - Each tracking device must have a unique vehicle
fact EachTrackingDeviceMustHaveAUniqueVehicle{
	all disj v1, v2: Vehicle | v1 != v2 implies v1.tracker != v2.tracker

}

//English - Each tracking device must belong to only one vehicle
fact EachTrackingDeviceMustHaveAUniqueVehicle{
	//all t1: TrackingDevice | t1 in Vehicle.tracker 
}

//English - All cell towers must have a range to tracking devices
//and the relation must only exist once
fact AllCellTowersHaveRangeToTrackingDevice{
	all t1: TrackingDevice,  c1: CellTower | one l1: Location
		| l1 -> c1 in t1.range
}

//English - All cell towers must have a communicationType to tracking devices
//and the relation must only exist once
fact AllCellTowersHaveCommunicationTypeToTrackingDevice{
	all t1: TrackingDevice, c1: CellTower | one com: Communication
		| com -> c1 in t1.communicationType
}

//English - A tracking device must only communicate with the cell tower in a specific
//type of communication based on its location to the cell tower i.e. Best - 4G and LTE,
//Acceptable - 3G, 4G, and LTE, Low - 3G and Edge and Out_Of_Range - None
fact CommunicationRelationToLocation {
//	all t1: TrackingDevice, com: Communication, cell: CellTower
//		| com -> cell in t1.communicationType
}


fact CommunicationRelationToWeather {
	
}

//English - Each tracker has a unique battery
fact uniqueTrackerBattery{
	all disj t1, t2: TrackingDevice | t1.track_dev_battery != t2.track_dev_battery
}

//English - The tracking device may only communicate with a 'other device' if 
//the tracking device is Out_Of_Range to a cell tower.
fact OnlyCommunicateWithOtherDeviceWhenOutofRange{

}


/**/
--Preds Scenarios

/*1 - The tracking device is far away from the cell tower, it's communication is 4G,
and the weather condition is good
*/
pred ScenarioOne[]{
	#Vehicle > 1 --some Vehicle
	#TrackingDevice > 1 --some TrackingDevice
	#CellTower > 1 --some CellTower
	some TrackingDevice.range 
	some GoodWeather
	some TrackingDevice.communicationType
	some TrackingDevice.range

} run ScenarioOne for 7 expect 1

/*2 - Multiple cell towers in a geographic location and at least one tower must be able to identify that
a tracking device is near a cell tower
*/


/*3 - The tracking device is near a cell tower, inside the geofence but the weather condition
is bad resulting in poor communication


/*4 - The tracking device is out of range of cell tower, so it interacts with the other device,
*/


/*5 - The tracking device is near a cell tower, outside of it's geofence, weather condition is good
The tracking device supports LTE
*/



// - Tracking device
// - geofence
// - weather conditions
// - cell towers
// - communication type( 3G, LTE, 4G)


//To Do or Discuss
/*
1. Should the communicationType only exist once between a tracking
device and the cell tower? Can it only communicate with one cell tower 
at a time? If so how do we say that, or does this relation show that?




*/