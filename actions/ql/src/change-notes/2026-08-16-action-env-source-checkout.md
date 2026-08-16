---
category: query
---
* The `actions/untrusted-checkout/critical` query now tracks environment variables exported by modeled actions through step, job, and reusable-workflow outputs. This detects privileged checkout and execution when `qinsoon/comment-env-vars` imports repository and ref values from pull request comments, including execution commands supplied by the concrete reusable-workflow caller.