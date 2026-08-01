---
category: minorAnalysis
---
* The `actions/artifact-poisoning/critical` and `actions/artifact-poisoning/medium` queries now account for event-aware execution reachability when assigning severity. A sink that cannot execute for a privileged trigger event is no longer reported as critical for that event.