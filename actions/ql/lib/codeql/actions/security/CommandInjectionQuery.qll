private import actions
private import codeql.actions.TaintTracking
private import codeql.actions.dataflow.ExternalFlow
import codeql.actions.dataflow.FlowSources
import codeql.actions.DataFlow
import codeql.actions.security.ControlChecks
private import codeql.actions.IntegratedExpressionControlFlow as IntegratedCfg

private class CommandInjectionSink extends DataFlow::Node {
  CommandInjectionSink() { madSink(this, "command-injection") }
}

bindingset[sink, event]
pragma[inline_late]
predicate sinkMayExecuteForEvent(DataFlow::Node sink, Event event) {
  IntegratedCfg::mayExecuteForEvent(sink.asExpr(), event)
}

/** Gets a relevant execution context for the sink in CommandInjectionCritical.ql. */
WorkflowExecutionContext getRelevantContextInPrivilegedContext(DataFlow::Node sink) {
  result = getAPrivilegedWorkflowExecutionContext(sink.asExpr()) and
  not exists(ControlCheck check |
    check.protects(sink.asExpr(), result.getEvent(), ["command-injection", "code-injection"])
  )
}

Event getRelevantEventInPrivilegedContext(DataFlow::Node sink) {
  result = getRelevantContextInPrivilegedContext(sink).getEvent()
}

bindingset[sink]
pragma[inline_late]
predicate sinkMayExecuteOnlyInNonPrivilegedContext(DataFlow::Node sink) {
  exists(Job job |
    job = sink.asExpr().getEnclosingJob() and
    (
      not exists(job.getATriggerEvent())
      or
      exists(Event event |
        job.getATriggerEvent() = event and
        sinkMayExecuteForEvent(sink, event) and
        getAWorkflowExecutionContextForNode(sink.asExpr()).getEvent() = event
      ) and
      not exists(Event event |
        job.getATriggerEvent() = event and
        sinkMayExecuteForEvent(sink, event) and
        getAPrivilegedWorkflowExecutionContext(sink.asExpr()).getEvent() = event
      )
    )
  )
}

/** Holds if `source` can reach `sink`, but not in a privileged execution context. */
predicate sourceMayReachOnlyNonPrivilegedContext(DataFlow::Node source, DataFlow::Node sink) {
  not exists(sink.asExpr().getEnclosingJob().getATriggerEvent())
  or
  exists(WorkflowExecutionContext context |
    source.(RemoteFlowSource).isUntrustedIn(context) and
    context.mayExecute(sink.asExpr()) and
    not context.isPullRequest()
  ) and
  not exists(WorkflowExecutionContext context |
    source.(RemoteFlowSource).isUntrustedIn(context) and context.isPrivileged(sink.asExpr())
  )
}

/**
 * A taint-tracking configuration for unsafe user input
 * that is used to construct and evaluate a system command.
 */
private module CommandInjectionConfig implements DataFlow::ConfigSig {
  predicate isSource(DataFlow::Node source) { source instanceof RemoteFlowSource }

  predicate isSink(DataFlow::Node sink) { sink instanceof CommandInjectionSink }

  predicate observeDiffInformedIncrementalMode() { any() }

  Location getASelectedSourceLocation(DataFlow::Node source) { none() }

  Location getASelectedSinkLocation(DataFlow::Node sink) {
    result = sink.getLocation()
    or
    result = getRelevantEventInPrivilegedContext(sink).getLocation()
  }
}

/** Tracks flow of unsafe user input that is used to construct and evaluate a system command. */
module CommandInjectionFlow = TaintTracking::Global<CommandInjectionConfig>;
