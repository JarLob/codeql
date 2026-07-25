---
category: minorAnalysis
---
* Privilege-sensitive GitHub Actions queries now account for effective `GITHUB_TOKEN` permissions across reusable workflow calls and direct trigger paths. In particular, `actions/improper-access-control` and `actions/cache-poisoning/poisonable-step` now distinguish direct-trigger privileges from caller-capped reusable invocations. Called workflows can maintain or reduce caller permissions, but attempted permission elevation is no longer treated as effective.
