---
category: minorAnalysis
---
* GitHub Actions security queries no longer report non-code findings that can execute exclusively in GitHub's isolated `pull_request` context. Code injection in that context is now reported by the new low-severity query `actions/code-injection/low`. Findings for other trigger contexts and event-independent workflow hardening remain unchanged.