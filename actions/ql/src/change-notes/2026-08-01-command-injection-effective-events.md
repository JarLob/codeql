---
category: minorAnalysis
---
* The `actions/command-injection/critical` and `actions/command-injection/medium` queries now account for job-level event filters when assigning severity. A job that cannot execute for a privileged trigger event is no longer reported as critical for that event.