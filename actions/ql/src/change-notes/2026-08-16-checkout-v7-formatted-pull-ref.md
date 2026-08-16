---
category: minorAnalysis
---
* The GitHub Actions analysis now recognizes pull request `head` and `merge` refs built with `format` and `github.event.pull_request.number` as protected by the `actions/checkout` v7 fork guard. This reduces false positive untrusted checkout results in `pull_request_target` workflows.