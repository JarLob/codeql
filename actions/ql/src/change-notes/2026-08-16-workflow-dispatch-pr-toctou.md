---
category: query
---
* The `actions/untrusted-checkout-toctou/critical` and `actions/untrusted-checkout-toctou/high` queries now detect manually dispatched checkouts of mutable pull request refs. The dispatch authorizes the selected pull request, but an attacker may change its code before checkout unless the approval is bound to an immutable reviewed commit.