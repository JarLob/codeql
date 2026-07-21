---
category: feature
---
* Added event-aware, three-valued evaluation for parsed GitHub Actions expressions through `evaluatesToBoolean`, `mayEvaluateToBoolean`, and `isConditionFeasible`, including status-check evaluation for known prerequisite-job conclusions. Job and step `if` conditions are now represented in the Actions control-flow graph with true and false successors. `ExpressionControlFlow` exposes expression-level short-circuit transitions and reachability for `!`, `&&`, and `||`; `IntegratedExpressionControlFlow` and `IntegratedExpressionBasicBlocks` connect those transitions to the shared Actions graph, basic blocks, and dominance; and `JobSynchronization` models job dependencies as a synchronization DAG with explicit job conclusions.
