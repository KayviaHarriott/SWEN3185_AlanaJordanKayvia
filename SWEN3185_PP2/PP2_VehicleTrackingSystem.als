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
	experience: one Experience,
	weather: Weather
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
one sig Excellent, Good, Okay, Poor extends Experience {}

pred sanityCheck[
]{
	some Vehicle
	some Engine
	some TrackingDevice
	some CellTower
	some Location
	some Vehicle.tracker
} run sanityCheck for 7 expect 1

/**Constraints/Invariants(?)**/

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
	all t1: TrackingDevice | one t1.range
}

//English - If a tracking device is off then it should not have a communication
//type to the cell tower
fact NoCommunicationTypeIfTrackingDeviceOff {
	all t1: TrackingDevice |  t1.status = Off implies no t1.communicationType

}

//English - If a vehicle engine status is off, so is tracking device
fact NoCommunicationTypeIfTrackingDeviceOff {
	all t1: TrackingDevice, veh: Vehicle |  veh.engine.status = Off implies t1.status = Off

}


//English - A tracking device must only communicate with the cell tower in a specific
//type of communication based on its location to the cell tower i.e. Best - 4G and LTE,
//Acceptable - 3G, 4G, and LTE, Low - 3G and Edge and Out_Of_Range - None
--EDGE, LTE, 3G, 4G
fact CommunicationRelationToLocationOutOfRange { 
	
	all t: TrackingDevice | dom[t.range] = Level_0 implies dom[t.communicationType] = None and t.experience = Poor
	all t: TrackingDevice | dom[t.communicationType] = None implies dom[t.range] = Level_0
	all t: TrackingDevice | dom[t.range] = Level_1 implies t.experience = Poor

	all t: TrackingDevice | dom[t.range] = Level_2 and dom[t.communicationType] = EDGE implies t.experience = Poor
	all t: TrackingDevice | dom[t.range] = Level_2 and dom[t.communicationType] = Com_3G implies t.experience = Okay
	all t: TrackingDevice | dom[t.range] = Level_2 and dom[t.communicationType] = Com_4G implies t.experience = Okay
	all t: TrackingDevice | dom[t.range] = Level_2 and dom[t.communicationType] = LTE implies t.experience = Okay

	all t: TrackingDevice | dom[t.range] = Level_3 and dom[t.communicationType] = EDGE implies t.experience = Okay
	all t: TrackingDevice | dom[t.range] = Level_3 and dom[t.communicationType] = Com_3G implies t.experience = Good
	all t: TrackingDevice | dom[t.range] = Level_3 and dom[t.communicationType] = Com_4G implies t.experience = Good
	all t: TrackingDevice | dom[t.range] = Level_3 and dom[t.communicationType] = LTE implies t.experience = Excellent

	all t: TrackingDevice | dom[t.range] = Level_4 and dom[t.communicationType] = EDGE implies t.experience = Okay
	all t: TrackingDevice | dom[t.range] = Level_4 and dom[t.communicationType] = Com_3G implies t.experience = Good
	all t: TrackingDevice | dom[t.range] = Level_4 and dom[t.communicationType] = Com_4G implies t.experience = Excellent
	all t: TrackingDevice | dom[t.range] = Level_4 and dom[t.communicationType] = LTE implies t.experience = Excellent

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
/*1
The tracking device is far away from the cell tower which means there are no CommunicationTypes available
and automatically create a connection with another device
*/
pred ScenarioOne[t1: TrackingDevice]{
	gt[#Vehicle,1] 
	gt[#TrackingDevice,1]
	gt[#CellTower,1] 
	
	dom[t1.range] = Level_0
	
} run ScenarioOne for 3 expect 1

/*2
Multiple cell towers in a geographic location and at least one tower must be able to identify that
a tracking device is near a cell tower.
*/
pred ScenarioTwo[c: CellTower]{
	gt[#Vehicle,1]
	gt[#CellTower,1]
	some TrackingDevice.communicationType.c 
} run ScenarioTwo for 7 expect 1

/*3
The tracking device is near a cell tower,
but the weather condition is bad resulting in poor or okay experience.
*/
pred ScenarioThree[t: TrackingDevice]{
	dom[t.range] = Level_3
	t.weather = UnsuitableWeather

} run ScenarioThree for 7 expect 1

/*4 - Vehicle has left geofence and should have an alert 
*/
pred ScenarioFour[t: TrackingDevice]{
	some t.recentGeofence

} run ScenarioFour for 7 expect 1

/*5 - The tracking device is near a cell tower, outside of it's geofence, 
weather condition is good and the tracking device supports LTE
*/
pred ScenarioFive[t: TrackingDevice]{
	dom[t.range] = Level_4
	some t.recentGeofence
	t.weather = GoodWeather

} run ScenarioFive for 7 expect 1
