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
	status: Status
}

sig TrackingDevice{
	track_dev_battery: Battery, --look into the strength of this battery
	sim_card: SimCard,
	status: Status,
	communication: Communication -> CellTower
}

sig OtherDevice{
	range: Location -> TrackingDevice,
	communication: Communication -> CellTower
}

sig CellTower{
	signal_strength: Bar,
	communication: Communication -> (TrackingDevice+OtherDevice)
}

sig Longitude, Latitude{}

sig SimCard{
	imei: IMEI,
	ser_num: SerialNumber
}  

sig IMEI, SerialNumber{}

sig Battery{
	status: Status --dont need since engine being on implies that the battery on
}

sig Geofence{}

abstract sig Communication{}
one sig EDGE, Com_3G, Com_4G, LTE extends Communication{}

abstract sig Status{}
one sig On, Off extends Status {}

abstract sig Bar{}
one sig Level_1, Level_2, Level_3, Level_4 extends Bar{}

abstract sig TimeInterval{}
one sig Few, Often, Persistent extends TimeInterval {}

abstract sig Weather {}
//one sig GoodWeather, SuitableWeather, BadWeather, UnsuitableWeather extends Weather {}
one sig Rain, Fog, Cloudy, Thunderstorm, Windy, Sunny, ModerateTemperature, Clear extends Weather{}

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
	some SimCard
	some Geofence
	some Vehicle.tracker
	some v: Vehicle | v.tracker.status = On
	some v: Vehicle | v.tracker.status = Off
	some range
	some TrackingDevice.communication
	some CellTower.communication
	some OtherDevice.communication

} run sanityCheck for 7 expect 1

/**Constraints/Invariants(?)**/

//English - The tracker must be configured correctly to send signals i.e.
//the tracker is attached to a vehicle engine and vehicle battery
//and must have a network registered sim card

//English - To send a signal related to the vehicle engine's the tracker must
//be connected to the engine

//English - The tracker must only be able to send a signal that is
//equivalent/same as the engine's state i.e. 'On' or 'Off'

//English - The tracking device must be 'in-range' or 'suitable' to a cell
//tower to be able to send and receive signals to and from the cell tower


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

//English - Each Vehicle has their own Engine
fact eachVehicleOwnEngine{
	all disj v1, v2: Vehicle | v1.engine != v2.engine
}

//English - If a device communicates with a cell tower with a particular 
//wireless communication, then the cell tower must communicate with the 
//same wireless communication and vice versa

fact sameWirelessCommunicationBetweenDevices{
	--tracking device , other device, cell tower , wireless communication

all d:TrackingDevice, o:OtherDevice, c:CellTower, com:Communication | 

	--If a tracking device or other device is in the relation communication
	(com->c in d.communication implies com->d in c.communication )
	and 
	(com->c in o.communication implies com->d in c.communication)
	
	

	--then the cell tower is in the same relation of communication


	--TrackingDevice, communication ------ Communication -> CellTower
	--OtherDevice, communication ------ Communication -> Celltower
	--CellTower, communication ----- Communication -> (TrackingDevice+OtherDevice)



}



//English - Each Battery has their own Status	
//fact eachBatteryHasOwnStatus{
//	//When I run this, it keeps solving and never ends
// 	all disj b1, b2: Battery | b1.status != b2.status
// }


//English - Each Battery is associated with a vehicle


//English - The tracking devices' battery status cannot be on
//if the vehicle battery status is off
fact trackingDeviceOnIfVehicleBatteryOn{
	all v: Vehicle | {
		v.battery.status = On implies v.tracker.status = On
		v.battery.status = Off implies v.tracker.status = Off
		}
}

//English - Each battery must be associated with only one device i.e.
//Vehicle, Tracking Device
fact allBatteryAssociatedWithOneDevice{
	all t: TrackingDevice, v: Vehicle |
		v.battery != t.track_dev_battery
}

//English - Each vehicle battery is unique
fact eachVehicleBatteryUnique{
	all disj v1, v2: TrackingDevice | v1.track_dev_battery != v2.track_dev_battery
}


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

--Ask Ms how to represent coordinates, should it be a set?
--or
--coordinates: Longitude -> Latitude


