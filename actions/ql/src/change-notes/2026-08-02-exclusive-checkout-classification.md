---
category: minorAnalysis
---
* The untrusted checkout, checkout TOCTOU, and improper access control queries now use a shared, mutually exclusive checkout classification. This removes duplicate high-severity findings for comment-authorized checkouts that lack effective revision binding.
