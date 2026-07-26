---
category: minorAnalysis
---
* The `actions/untrusted-checkout-toctou` queries now report mutable pull request checkouts guarded only by a label or deployment environment approval. Deployment environments are treated as access-control checks only when repository metadata identifies an enabled required-reviewer capability; wait timers, explicitly disabled reviewer gates, and environments without protection metadata no longer suppress ordinary untrusted checkout findings.
