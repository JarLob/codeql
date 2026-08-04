---
category: minorAnalysis
---
* GitHub Actions analysis now correlates `workflow_run` triggers with named local workflows, source events, branch filters, and source-specific conditions. This improves results for privileged checkout, injection, artifact poisoning, cache poisoning, secret exfiltration, and self-hosted runner queries while accounting for GitHub's fork-origin protection on positive `workflow_run.branches` filters.
