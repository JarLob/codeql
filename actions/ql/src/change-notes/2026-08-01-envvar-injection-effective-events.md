---
category: minorAnalysis
---
* The `actions/envvar-injection/critical` and `actions/envvar-injection/medium` queries now account for job-level event filters when assigning severity. A job that cannot execute for a privileged trigger event is no longer reported as critical for that event.