---
category: query
---
* The `actions/code-injection/critical` query now accounts for the principal controlling each data-flow source when applying authorization checks. In particular, an `issue_comment` association check for the triggering commenter no longer suppresses pull request metadata read through `gh pr` or `gh api ... pulls`, because that data remains controlled by the pull request author.