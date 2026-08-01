---
category: minorAnalysis
---
* The `actions/improper-access-control` query now recognizes conditions proving that
  `github.event.pull_request.head.repo.fork` is false as same-repository restrictions.