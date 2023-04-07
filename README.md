# Updates Recommended & Status

---
## Ms Suggestions
- [x] Change SignalStrengths to Service level or signal strength 
- [x] how the TD communicates with towers based on the weather
    - we added a relation of location to CellTower
- [x] Why is weather linked to tracking device ? Weather in location . Why doesn’t the location know about the weather. Location should have weather field. 
    - we added that Location has relation weather, and weather was removed from TrackingDevice
- [ ] Experience is tied to weather and location , where the cell tower is also affects this. 
    - thinking that it means experience affects the original communication of the cell tower
- [ ] Go through location to cell tower 
    -  we're thinking this meant add the location relation to cell tower
- [x] Cell tower needs to be linked location
- [x] Possible merge communication type and range (SignalStrength)
    - we did this by changing communicationType CellTower -> Communication -> SignalStrength
- Comtype to SignalStrength to cell tower should be the same 
    - I think this was done, unsure
- [x] Have to model that the other device is allowing to communicate (permissions)*important*
    - Added relation permissions: Status -> OtherDevice
- [x] Combining suitable and good weather 
    - Combined to 'Suitable Weather'
- [x] Remove battery as a signature 
- Geofences is higher order relation
    - what is higher order?
- [x] Why do we need recentgeofence ? Can have a function that gets last location 
    - Removed recentGeofence
- Activegeofence is history of location 
- [x] If it’s not a location in geofence then it sends an alert 
    - thinking to write a fact to say if not in location of geofence then it's an alert
- [x] Map is location -> location , strongly connected 
    - [x]Geofence : location-> location , structure of a ring ( one loop)
    - we made a map signature and added the relation geofence: location -> location
- [ ] Active : seq location 
    - wondering what this means
- [x] Weather is about location 

---
## Variables
- Engine status

---
## Operations
- Movement
- Change weather
- Change status
- function gets the last location

---
## To Do
- [ ] Clarify the geofences
- [ ] Make location relation in tracking device sequence
- [ ] Ensure that location is sequential
- [ ] Ensure that the location

---
## Additional Changes Made
- Cell tower is in location 
- removed recent geofences



