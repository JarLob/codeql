---
category: minorAnalysis
---
* The `actions/untrusted-checkout-toctou/critical` query now detects pull request code checked out by commit SHA when a persistent label approval can be reused by a `synchronize` or `reopened` `pull_request_target` activity. This also applies when the approval and checkout are separated by nested reusable workflows.
