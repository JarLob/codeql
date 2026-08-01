---
category: minorAnalysis
---
* The `actions/argument-injection/critical` and `actions/argument-injection/medium` queries now account for job-level event filters when assigning severity. A job that cannot execute for a privileged trigger event is no longer reported as critical for that event.