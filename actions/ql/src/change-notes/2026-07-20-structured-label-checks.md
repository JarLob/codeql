---
category: minorAnalysis
---
* Workflow access-control checks are now recognized from parsed GitHub Actions expression structure. A parsed condition is protective only when every feasible true path contains an effective label, actor, association, or repository check. This improves handling of conjunctions, disjunctions, nested and negated checks, and bypass alternatives while retaining regex fallback for expressions that cannot yet be parsed.