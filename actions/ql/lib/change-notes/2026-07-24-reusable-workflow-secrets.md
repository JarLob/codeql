---
category: feature
---
* Added modeling for reusable-workflow secret declarations, named secret mappings, and `secrets: inherit`. Named mappings participate in interprocedural data flow, while inherited secrets are exposed as a call-site capability. The `Uses.isRemoteCall()` predicate distinguishes remote actions and reusable workflows from local calls.
