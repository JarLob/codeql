---
category: feature
---
* Added `MatrixCombination`, `Strategy.getAMatrixCombination()`, and `Strategy.hasExactMatrixCombinations()` to model bounded effective GitHub Actions matrix combinations after `exclude` and ordered `include` processing. Matrix job synchronization now uses these values, modeling up to 16 effective combinations from a bounded 256-combination Cartesian expansion. Static structured axis values retain exact expansion when structured comparison is not required; dynamic or larger matrices fall back to a wildcard.