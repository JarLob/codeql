---
category: feature
---
* Added event-aware, three-valued evaluation for parsed GitHub Actions expressions through `evaluatesToBoolean`, `mayEvaluateToBoolean`, and `isConditionFeasible`, including status-check evaluation after skipped prerequisite jobs. Job and step `if` conditions are now represented in the Actions control-flow graph with true and false successors, and `ExpressionControlFlow` exposes expression-level short-circuit transitions and reachability for `!`, `&&`, and `||`.