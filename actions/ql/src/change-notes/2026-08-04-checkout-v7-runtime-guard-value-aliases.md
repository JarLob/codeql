---
category: minorAnalysis
---
* The GitHub Actions analysis now recognizes `actions/checkout` v7 runtime guard inputs passed through declarative value aliases, including workflow, job, or step environment variables and job outputs. This reduces false positive untrusted checkout, environment and PATH injection, output clobbering, and cache poisoning results.