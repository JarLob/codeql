---
category: query
---
* The `actions/untrusted-checkout/critical` query now detects externally influenced code imported into an automated same-repository pull request and executed by a credential-bearing `pull_request` workflow after automation satisfies an exact label, event-actor, or pull-request-author control.