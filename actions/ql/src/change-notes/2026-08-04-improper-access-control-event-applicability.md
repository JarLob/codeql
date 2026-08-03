---
category: minorAnalysis
---
* The `actions/improper-access-control` query now accounts for event-specific condition branches when identifying checkout authorization attempts. This removes false positive results where an authorization check, such as a pull request label check, is not evaluated for the reported trigger event.