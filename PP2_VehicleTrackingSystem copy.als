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
	battery: lone Battery,
	engine: Engine
}

sig Engine{
	status: Status
}

sig TrackingDevice{
	track_dev_battery: Battery, --look into the strength of this battery
	--sim_card: SimCard,-- say it's implied that it has the sim card already in it so remove it//Ask Ms 
	status: Status,
	communicationType: Communication -> CellTower,
	range: Location -> CellTower,
	connection: Location -> OtherDevice, -- only populated if the raneg is OutOfRange
	geofences: Location -> Location, -- all the geofences of the user --Ms: Location -> Location, how do we say it's out the boundary
	activeGeofence: geofences,
	recentGeofence: geofences,
	alert: Alert -> (activeGeofence+recentGeofence) --States: you are alerted once entered or left
	-- entered disappears when you have left and left disappears when you enter a new
	
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

--sig Longitude, Latitude{}

--sig SimCard{
	--imei: IMEI, -- remove but mention in the document
	--ser_num: SerialNumber
--}  

--sig IMEI, SerialNumber{}

sig Battery{}

--sig Geofence{}
--Geofence should be a relation, that maps location to location and that can be used to 
--draw a graph

abstract sig Communication{}
one sig None, EDGE, Com_3G, Com_4G, LTE extends Communication{} --MK: does this affect 
-- signal strength of Cell Tower? and if so... based on Cell Tower, signal_strength
-- would be better in this sig
-- if signal_strength is affected by distance from tower and communication type then
-- it should be inside the tracker itself


abstract sig Status{}
one sig On, Off extends Status {}

abstract sig Bar{}
one sig Level_1, Level_2, Level_3, Level_4 extends Bar{}

--abstract sig TimeInterval{}
--one sig Few, Often, Persistent extends TimeInterval {} -- ask Ms about this

abstract sig Weather {}
one sig GoodWeather, SuitableWeather, BadWeather, UnsuitableWeather extends Weather {}
--one sig Rain, Fog, Cloudy, Thunderstorm, Windy, Sunny, ModerateTemperature, Clear extends Weather{}
--

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
	--some SimCard
	//some Geofence
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

//English - 
fact CommunicationRelationToLocation {
	// all t1: TrackingDevice, l1: Location, c1: CellTower, com1: Communication |
	// 	(l1 -> c1 in t1.range and l1 = Best) implies 
	// 			( com1 -> c1 in t1.communicationType and com1 = (Com_4G+LTE))
		
	// all t1: TrackingDevice, l1: Location, c1: CellTower, com1: Communication |
	// 	(l1 -> c1 in t1.range and l1 = Acceptable) implies 
	// 			( com1 -> c1 in t1.communicationType and com1 = (Com_3G+Com_4G+LTE))
		
	// all t1: TrackingDevice, l1: Location, c1: CellTower, com1: Communication |
	// 	(l1 -> c1 in t1.range and l1 = Low) implies 
	// 			( com1 -> c1 in t1.communicationType and com1 = (Com_3G+EDGE))

	all t1: TrackingDevice, l1: Location, c1: CellTower, com1: Communication |
		((l1 -> c1 in t1.range and l1 = Best) implies 
				( com1 -> c1 in t1.communicationType and com1 = (LTE)))

	and 

		((l1 -> c1 in t1.range and l1 = Acceptable) implies 
				( com1 -> c1 in t1.communicationType and com1 = (Com_4G)))
		
	and
		((l1 -> c1 in t1.range and l1 = Low) implies 
				( com1 -> c1 in t1.communicationType and com1 = (Com_3G)))
	
	// and 
	// 	((l1 -> c1 in t1.range and l1 = Out_Of_Range) implies 
	// 			( com1 -> c1 in t1.communicationType and com1 = (None)))
		
	// all t1: TrackingDevice, l1: Location, c1: CellTower|
	// 	(l1 -> c1 in t1.range and l1 = Out_Of_Range) implies 
	// 			( com1 -> c1 in t1.communicationType and com1 = (EDGE))



	--Best, 4G and LTE

	-- Acceptable, 3G, 4G, and LTE

	-- Low, 3G, Edge

	--Out of Range, none 
}

//look at this Kayvia
--i think ask Ms
fact CommunicationRelationToLocation {
	all t1: TrackingDevice, l1: Location, c1: CellTower, com1: Communication |
		(l1 -> c1 in t1.range and l1 = Best) implies 
				( com1 -> c1 in t1.communicationType and com1 = (Com_4G+LTE))
	and

		(l1 -> c1 in t1.range and l1 = Acceptable) implies 
				( com1 -> c1 in t1.communicationType and com1 = (Com_3G+Com_4G+LTE))
	and
		(l1 -> c1 in t1.range and l1 = Low) implies 
				( com1 -> c1 in t1.communicationType and com1 = (Com_3G+EDGE))
	and
		(l1 -> c1 in t1.range and l1 = Out_Of_Range) implies 
				( com1 -> c1 in t1.communicationType and com1 = (none))
}

fact CommunicationRelationToWeather {

}



//English - The tracker must be configured correctly to send signals i.e.
//the tracker is attached to a vehicle engine and vehicle battery
//and must have a network registered sim card

//English - To send a signal related to the vehicle engine's the tracker must
//be connected to the engine

//English - The tracker must only be able to send a signal that is
//equivalent/same as the engine's state i.e. 'On' or 'Off'

//English - The tracking device must be 'in-range' or 'suitable' to a cell
//tower to be able to send and receive signals to and from the cell tower


//English - Each tracker has a unique battery
fact uniqueTrackerBattery{
	all disj t1, t2: TrackingDevice | t1.track_dev_battery != t2.track_dev_battery
}

//English - Each SimCard has a unique IMEI
// fact uniqueIMEIForSimCard{
// 	all disj s1, s2: SimCard | s1.imei != s2.imei 
// }

// //English - Each SimCard has a unique SerialNumber
// fact uniqueSerialNumberForSimCard{
// 	all disj s1, s2: SimCard | s1.ser_num != s2.ser_num	
// }

// //English - Each Vehicle has their own Battery
// fact eachVehicleOwnBattery{
// 	all disj v1, v2: Vehicle | v1.battery != v2.battery
// }

// //English - Each Vehicle has their own Engine
// fact eachVehicleOwnEngine{
// 	all disj v1, v2: Vehicle | v1.engine != v2.engine
// }

// //English - If a device communicates with a cell tower with a particular 
// //wireless communication, then the cell tower must communicate with the 
// //same wireless communication and vice versa

// fact sameWirelessCommunicationBetweenDevices{
// 	--tracking device , other device, cell tower , wireless communication

// all d:TrackingDevice, o:OtherDevice, c:CellTower, com:Communication | 

// 	--If a tracking device or other device is in the relation communication
// 	(com->c in d.communication implies com->d in c.communication )
// 	and 
// 	(com->c in o.communication implies com->d in c.communication)
	
	

// 	--then the cell tower is in the same relation of communication


// 	--TrackingDevice, communication ------ Communication -> CellTower
// 	--OtherDevice, communication ------ Communication -> Celltower
// 	--CellTower, communication ----- Communication -> (TrackingDevice+OtherDevice)



// }



//English - Each Battery has their own Status	
//fact eachBatteryHasOwnStatus{
//	//When I run this, it keeps solving and never ends
// 	all disj b1, b2: Battery | b1.status != b2.status
// }


//English - Each Battery is associated with a vehicle


//English - The tracking devices' battery status cannot be on
//if the vehicle battery status is off
// fact trackingDeviceOnIfVehicleBatteryOn{
// 	all v: Vehicle | {
// 		v.battery.status = On implies v.tracker.status = On
// 		v.battery.status = Off implies v.tracker.status = Off
// 		}
// }

// //English - Each battery must be associated with only one device i.e.
// //Vehicle, Tracking Device
// fact allBatteryAssociatedWithOneDevice{
// 	all t: TrackingDevice, v: Vehicle |
// 		v.battery != t.track_dev_battery
// }

// //English - Each vehicle battery is unique
// fact eachVehicleBatteryUnique{
// 	all disj v1, v2: TrackingDevice | v1.track_dev_battery != v2.track_dev_battery
// }


// assert simCardUniqueIMEI{
// 	no disj s1, s2: SimCard | s1.imei = s2.imei

// }check simCardUniqueIMEI for 7 expect 0

// assert simCardUniqueSerialNumber{
// 	no disj s1, s2: SimCard | s1.ser_num = s2.ser_num

// }check simCardUniqueSerialNumber for 7 expect 0

fact OnlyCommunicateWithOtherDeviceWhenOutofRange{
	-- tracking device only with 
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





//Questions to Ask Ms
--ask Ms if we should use facts and call preds or if we should use facts alone
--up to us

--should battery be specified for both the vehicle and tracking device, while including the engine and tracking device itself

--Ask Ms how to represent coordinates, should it be a set?
--or
--coordinates: Longitude -> Latitude


//_____
//Maybe if the tracking device is in the location of the Geofence
//the battery of the device itself would determine how long the geofence is available

//Specificy what a geofence is and how it's created, based on tower to tower?
//Maybe the distance between a cell tower to a cell tower

//Geofence uses a polygon of 3 to 5 sides, we use graphs and say it is acyclic
//graphs,
--ask miss about communication types and hoow  it relates to location and geofence
--ask about predicates and how to write them if we can say #Vehicles >