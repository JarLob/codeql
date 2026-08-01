---
category: minorAnalysis
---
* The `actions/output-clobbering/high` query now accounts for event-aware execution reachability. A sink that cannot execute for a privileged trigger event is no longer reported for that event.