---
category: minorAnalysis
---
* The `actions/artifact-poisoning/path-traversal` query now accounts for event-aware execution reachability. A vulnerable artifact download that cannot execute for a privileged trigger event is no longer reported for that event.