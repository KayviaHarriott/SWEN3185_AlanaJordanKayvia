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
	tracker: lone TrackingDevice,
	battery: Battery,
	engine: Engine
}

sig Engine{
	
}
sig TrackingDevice{
	track_dev_battery: Battery,
	sim_card: SimCard,
	status: Status
}

sig CellTower{
	coordinates: set Coordinate --I think this may be a set, unsure
	--or
	--coordinates: Longitude -> Latitude
}

--sig Longitude, Latitude

sig Coordinate{
	-- Longtitude, Laitude
}



sig SimCard{
	imei: IMEI,
	ser_num: SerialNumber
}  

sig IMEI, SerialNumber{}

sig Battery{
	status: Status
}

sig Geofence{}

//abstract sig BatteryStatus{}
//one sig On, Off extends BatteryStatus {}
--I think this should be status instead and used for both battery
-- and engine, but unsure, ask Ms how to model with abstract

// abstract sig CoordinateT{}
// one sig Longitude, Latitude extends Status {}

abstract sig Status{}
one sig On, Off extends Status {}

abstract sig TimeInterval{}
one sig Few, Often, Persistent extends TimeInterval {}

abstract sig Weather {}
one sig Good, Suitable, Bad, Unsuitable extends Weather {}


pred a_simple_vehicle_tracking_system[
]{
	#Vehicle > 3
	#SimCard > 3

} run a_simple_vehicle_tracking_system for 7 expect 1


//English - Each SimCard has a unique IMEI
fact uniqueIMEIForSimCard{
	all disj s1, s2: SimCard | s1.imei != s2.imei 
}

//English - Each SimCard has a unique SerialNumber
fact uniqueSerialNumberForSimCard{
	all disj s1, s2: SimCard | s1.ser_num != s2.ser_num	
}

//English - Each Vehicle has their own Battery
fact eachVehicleOwnBattery{
	all disj v1, v2: Vehicle | v1.battery != v2.battery
}

//English - Each Battery has their own Status	
// fact eachBatteryHasOwnStatus{
// 	all disj b1, b2: Battery | b1.status != b2.status
// }

//English - Each Battery has a status associated with it


//English - Each Battery is associated with a vehicle


//English - The tracking devices' battery status cannot be on
//if the vehicle battery status is off



assert simCardUniqueIMEI{
	no disj s1, s2: SimCard | s1.imei = s2.imei

}check simCardUniqueIMEI for 7 expect 0

assert simCardUniqueSerialNumber{
	no disj s1, s2: SimCard | s1.ser_num = s2.ser_num

}check simCardUniqueSerialNumber for 7 expect 0



/**/
--Preds Scenarios

/*1 - A scenario where battery is on, tracking device is working
optimal, perfect scenario
*/


/*2 - A scenerio where the weather is bad

*/

/*3 - A scenario where the battery and the engine status is off


/*4 - A scenario where the tracking device is off and the engine status is on

*/


/*5 

*/

//Questions to Ask Ms
--ask Ms if we should use facts and call preds or if we should use facts alone

--should battery be specified for both the vehicle and tracking device, while including the engine and tracking device itself



