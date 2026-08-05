---
category: minorAnalysis
---
* Added `Event.acceptsActivityType` and `Event.hasFeasibleWorkflowRunActivityType` to model explicit and default event activity filters. `workflow_run` source correlation now excludes source triggers limited to activities that require repository privileges.