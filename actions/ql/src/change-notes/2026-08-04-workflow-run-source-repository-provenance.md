---
category: minorAnalysis
---
* GitHub Actions analysis now distinguishes source-run repository provenance when applying positive `workflow_run.branches` filters. Externally triggered `pull_request_review` and `pull_request_review_comment` runs can use the base repository and are no longer incorrectly filtered out as fork-head pull request runs. This improves detection of externally reachable privileged workflows triggered by reviews.