---
category: feature
---
* GitHub Actions event-aware control flow is now evaluated within the relevant expression or CFG scope instead of through a global event-indexed transitive closure. Exact `needs.*` assignments and matrix `continue-on-error` evaluation are independently bounded, with conservative aggregate fallbacks for larger workflows. Structural model generation and occurrence-keyed YAML anchor handling avoid importing event-aware filtering or materializing global job, step, and scalar products.