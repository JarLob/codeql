---
category: minorAnalysis
---
* GitHub Actions analysis now correlates `workflow_run` triggers with named local workflows, source events, ordered workflow-name and branch glob filters, and source-specific conditions. This improves results for privileged checkout, injection, artifact poisoning, cache poisoning, and secret exfiltration queries while matching GitHub's glob semantics and fork-origin protection on positive `workflow_run.branches` filters.
