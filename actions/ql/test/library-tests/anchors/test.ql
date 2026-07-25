import codeql.actions.Ast
import codeql.actions.Cfg as Cfg
import codeql.actions.DataFlow
import codeql.actions.TaintTracking
import codeql.actions.dataflow.FlowSources

private module AnchoredReusableFlowConfig implements DataFlow::ConfigSig {
  predicate isSource(DataFlow::Node source) {
    source instanceof RemoteFlowSource and
    source.asExpr().(GitHubExpression).getFieldName() = "event.comment.body"
  }

  predicate isSink(DataFlow::Node sink) {
    exists(Run run |
      run.getLocation().getFile().getBaseName() = "reusable-callee.yml" and
      run.getAnScriptExpr() = sink.asExpr()
    )
  }

  predicate observeDiffInformedIncrementalMode() { any() }
}

module AnchoredReusableFlow = TaintTracking::Global<AnchoredReusableFlowConfig>;

query predicate stepOwners(string step, string job) {
  exists(Step s |
    step = s.getLocation().toString() and
    job = s.getEnclosingJob().getId()
  )
}

query predicate expressionOwners(string expression, string job) {
  exists(Expression e |
    expression = e.toString() and
    job = e.getEnclosingJob().getId()
  )
}

query predicate effectivePermissions(string job, string permission) {
  exists(Job j |
    j.getLocation().getFile().getBaseName() = "forms.yml" and
    job = j.getId() and
    permission = j.getEffectivePermission("contents")
  )
}

query predicate runnerLabels(string job, string label) {
  exists(Job j |
    j.getLocation().getFile().getBaseName() = "forms.yml" and
    job = j.getId() and
    label = j.getARunsOnLabel()
  )
}

query predicate stepPositions(string job, int index, string step) {
  exists(LocalJob j, Step s |
    j.getLocation().getFile().getBaseName() = "forms.yml" and
    job = j.getId() and
    j.getStep(index) = s and
    step = s.getLocation().toString()
  )
}

query predicate stepCounts(string job, int stepCount) {
  exists(LocalJob j |
    j.getLocation().getFile().getBaseName() = "forms.yml" and
    job = j.getId() and
    stepCount = strictcount(j.getAStep())
  )
}

query predicate expressionCfgNodeCounts(string expression, int nodeCount) {
  expression = "github.event.comment.body" and
  nodeCount = strictcount(Cfg::Node node |
    exists(Expression e |
      e.getLocation().getFile().getBaseName() = "forms.yml" and
      e.toString() = expression and
      node.getAstNode() = e
    )
  |
    node
  )
}

query predicate localFlows(string source, string sink, string job) {
  exists(DataFlow::Node sourceNode, DataFlow::Node sinkNode, Run run |
    sourceNode instanceof RemoteFlowSource and
    sourceNode.asExpr().(GitHubExpression).getFieldName() = "event.comment.body" and
    run.getAnScriptExpr() = sinkNode.asExpr() and
    DataFlow::hasLocalFlow(sourceNode, sinkNode) and
    source = sourceNode.toString() and
    sink = sinkNode.toString() and
    job = run.getEnclosingJob().getId()
  )
}

query predicate reusableFlows(DataFlow::Node source, DataFlow::Node sink) {
  AnchoredReusableFlow::flow(source, sink)
}