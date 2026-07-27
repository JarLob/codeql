---
category: minorAnalysis
---
* The `actions/untrusted-checkout` queries now normalize checkout and local execution paths,
  including workspace expressions and Windows separators. Static matching paths are reported by
  the `critical` query without matching sibling or escaping paths, while unresolved dynamic paths
  retain a `high` fallback.
