---
category: minorAnalysis
---
* Cache-poisoning queries no longer consider a default-branch cache-write event when a job's `if` condition, or a transitive prerequisite job's condition, can be proven false for that event. Explicit status-check conditions are evaluated with skipped prerequisites, while conditions that cannot be evaluated remain conservatively feasible.
