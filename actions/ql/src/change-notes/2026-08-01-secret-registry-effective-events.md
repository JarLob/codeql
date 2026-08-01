---
category: minorAnalysis
---
* The `actions/secret-exfiltration` query now accounts for job-level event filters when detecting attacker-controlled container registries. A registry credential is no longer reported as exposed for a privileged trigger event excluded by the job condition.