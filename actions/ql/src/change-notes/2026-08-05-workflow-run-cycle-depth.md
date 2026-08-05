---
category: minorAnalysis
---
* GitHub Actions analysis now applies GitHub's cycle detection and three-level chaining limit when correlating local `workflow_run` sources. This reduces false positive results in workflows that GitHub blocks because they directly trigger themselves, repeat a workflow path in their chained ancestry, or form a fourth consecutive `workflow_run` level.