---
category: query
---
* The `actions/untrusted-checkout-toctou/critical` and `actions/untrusted-checkout-toctou/high` queries now recognize composite-action checkout inputs that every caller for the reported event explicitly binds to the base repository's default branch. This reduces false positive results caused by unrelated callers of the same composite action.