---
category: minorAnalysis
---
* GitHub Actions security queries no longer treat bypassable compound conditions as effective actor, association, label, or repository controls. Permission checks using `actions-cool/check-user-permission` are now recognized only when they explicitly require `write` or `admin` access and enforce that requirement through a matching failure step or the version-supported `error-if-missing` option. Comment freshness checks must convert distinct head-push and comment timestamps, and direct `jq` extraction must use `.head.repo.pushed_at` rather than the base repository timestamp.
