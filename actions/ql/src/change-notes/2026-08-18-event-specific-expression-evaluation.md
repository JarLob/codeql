---
category: minorAnalysis
---
* GitHub Actions expression evaluation now accounts for event-specific missing values and statically known reusable-workflow input defaults and caller bindings. This reduces false-positive cache poisoning and output clobbering results in multi-trigger and reusable workflows while preserving both outcomes for unknown values.