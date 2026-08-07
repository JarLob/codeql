private import actions
private import codeql.actions.TaintTracking
private import codeql.actions.dataflow.ExternalFlow
import codeql.actions.dataflow.FlowSources
import codeql.actions.DataFlow

private class RequestForgerySink extends DataFlow::Node {
  RequestForgerySink() { madSink(this, "request-forgery") }
}

/**
 * A taint-tracking configuration for unsafe user input
 * that is used to construct and evaluate a system command.
 */
private module RequestForgeryConfig implements DataFlow::ConfigSig {
  predicate isSource(DataFlow::Node source) { source instanceof RemoteFlowSource }

  predicate isSink(DataFlow::Node sink) { sink instanceof RequestForgerySink }

  predicate observeDiffInformedIncrementalMode() { any() }
}

/** Tracks flow of unsafe user input that is used to construct and evaluate a system command. */
module RequestForgeryFlow = TaintTracking::Global<RequestForgeryConfig>;

/** Holds if a request-forgery flow may execute outside an isolated pull request context. */
predicate requestForgeryInReportableContext(
  RequestForgeryFlow::PathNode source, RequestForgeryFlow::PathNode sink
) {
  RequestForgeryFlow::flowPath(source, sink) and
  (
    not exists(sink.getNode().asExpr().getEnclosingJob().getATriggerEvent())
    or
    exists(WorkflowExecutionContext context |
      source.getNode().(RemoteFlowSource).isUntrustedIn(context) and
      context.mayExecute(sink.getNode().asExpr()) and
      not context.isPullRequest()
    )
  )
}
