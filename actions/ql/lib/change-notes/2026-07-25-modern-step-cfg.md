---
category: feature
---
* Added typed GitHub Actions AST and control-flow support for background run/action steps, `wait`, `wait-all`, `cancel`, and `parallel` groups. Nested parallel children participate in AST, CFG, and data flow, while background completion is joined at the first matching barrier or workflow exit.