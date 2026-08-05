---
category: minorAnalysis
---
* GitHub Actions analysis now tracks externally controlled data through statically resolved same-repository calls to `benc-uk/workflow-dispatch` and `peter-evans/repository-dispatch`. This improves injection and other data-flow query results in programmatically dispatched workflows while correlating workflow inputs, repository payload properties, event types, and caller trigger provenance.