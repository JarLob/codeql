---
category: minorAnalysis
---
* The `actions/code-injection/critical` query now detects untrusted input used as a complete job container image when the job exposes a named secret or write-capable GitHub token. The `actions/cache-poisoning/code-injection` query detects attacker-selected job images that can poison the default-branch cache. The `actions/secret-exfiltration` query now detects registry credentials sent to a registry selected by an untrusted job or service container image.
