---
category: minorAnalysis
---
* The GitHub Actions analysis now accounts for the runtime fork pull request checkout guard in `actions/checkout` v7. This reduces false positive untrusted checkout, environment and PATH injection, output clobbering, and cache poisoning results. Findings are retained when the guard does not apply, including for other trigger events, older versions, checkout targets the guard cannot identify, and explicit or dynamic use of `allow-unsafe-pr-checkout`.
