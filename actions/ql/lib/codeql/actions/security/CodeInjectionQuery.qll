private import actions
private import codeql.actions.TaintTracking
private import codeql.actions.dataflow.ExternalFlow
import codeql.actions.dataflow.FlowSources
import codeql.actions.DataFlow
import codeql.actions.security.CodeInjectionSinks
import codeql.actions.security.ControlChecks
import codeql.actions.security.CachePoisoningQuery
private import codeql.actions.JobSynchronization as JobSync

private predicate isJobContainerImageSink(DataFlow::Node sink) {
  exists(LocalJob job | job.getJobContainerImageExpr() = sink.asExpr())
}

private predicate jobContainerHasSensitiveCapability(
  DataFlow::Node sink, WorkflowExecutionContext context
) {
  exists(LocalJob job |
    job.getJobContainerImageExpr() = sink.asExpr() and
    job.getATriggerEvent() = context.getEvent() and
    (
      exists(SecretsExpression secret |
        secret.getEnclosingJob() = job and secret.getFieldName() != "GITHUB_TOKEN"
      )
      or
      context.isPrivileged(sink.asExpr()) and
      (
        exists(SecretsExpression token |
          token.getEnclosingJob() = job and token.getFieldName() = "GITHUB_TOKEN"
        )
        or
        exists(GitHubExpression token |
          token.getEnclosingJob() = job and token.getFieldName() = "token"
        )
      )
    )
  )
}

private predicate sinkMayExecuteForEvent(DataFlow::Node sink, Event event) {
  JobSync::jobMayExecuteForEvent(sink.asExpr().getEnclosingJob(), event)
}

/**
 * Gets a relevant execution context for the sink in CodeInjectionCritical.ql.
 */
bindingset[sink]
pragma[inline_late]
WorkflowExecutionContext getRelevantCriticalContextForSink(DataFlow::Node sink) {
  result = getAPrivilegedWorkflowExecutionContext(sink.asExpr()) and
  sinkMayExecuteForEvent(sink, result.getEvent()) and
  (not isJobContainerImageSink(sink) or jobContainerHasSensitiveCapability(sink, result)) and
  not isGithubScriptUsingToJson(sink.asExpr())
}

/** Gets the event for a relevant critical execution context. */
Event getRelevantCriticalEventForSink(DataFlow::Node sink) {
  result = getRelevantCriticalContextForSink(sink).getEvent()
}

/**
 * Gets a relevant execution context for the sink in CachePoisoningViaCodeInjection.ql.
 */
WorkflowExecutionContext getRelevantCachePoisoningContextForSink(DataFlow::Node sink) {
  exists(LocalJob job, Event event |
    job = sink.asExpr().getEnclosingJob() and
    job.getATriggerEvent() = event and
    result = getAWorkflowExecutionContextForNode(sink.asExpr()) and
    result.getEvent() = event and
    // excluding privileged workflows since they can be exploited in easier circumstances
    // which is covered by `actions/code-injection/critical`
    not getAPrivilegedWorkflowExecutionContext(sink.asExpr()).getEvent() = event and
    hasDefaultBranchCacheWriteAccess(job, event)
  )
}

Event getRelevantCachePoisoningEventForSink(DataFlow::Node sink) {
  result = getRelevantCachePoisoningContextForSink(sink).getEvent()
}

/**
 * A taint-tracking configuration for unsafe user input
 * that is used to construct and evaluate a code script.
 */
private module CodeInjectionConfig implements DataFlow::ConfigSig {
  predicate isSource(DataFlow::Node source) { source instanceof RemoteFlowSource }

  predicate isSink(DataFlow::Node sink) { sink instanceof CodeInjectionSink }

  predicate isAdditionalFlowStep(DataFlow::Node pred, DataFlow::Node succ) {
    exists(Uses step |
      pred instanceof FileSource and
      pred.asExpr().(Step).getAFollowingStep() = step and
      succ.asExpr() = step and
      madSink(succ, "code-injection")
    )
    or
    exists(Run run |
      pred instanceof FileSource and
      pred.asExpr().(Step).getAFollowingStep() = run and
      succ.asExpr() = run.getScript() and
      exists(run.getScript().getAFileReadCommand())
    )
  }

  predicate observeDiffInformedIncrementalMode() { any() }

  Location getASelectedSinkLocation(DataFlow::Node sink) {
    result = sink.getLocation()
    or
    result = getRelevantCriticalEventForSink(sink).getLocation()
    or
    result = getRelevantCachePoisoningEventForSink(sink).getLocation()
  }
}

/** Tracks flow of unsafe user input that is used to construct and evaluate a code script. */
module CodeInjectionFlow = TaintTracking::Global<CodeInjectionConfig>;

private predicate controlProtectsCodeInjection(
  ControlCheck check, RemoteFlowSource source, DataFlow::Node sink, WorkflowExecutionContext context
) {
  check.protects(sink.asExpr(), context.getEvent(), "code-injection") and
  not exists(GhCLICommandSource commandSource |
    check instanceof AssociationCheck and
    context.getEvent().getName() = ["issue_comment", "pull_request_comment"] and
    source = commandSource and
    commandSource.getCommand().regexpMatch(".*\\b(pr|pulls)\\b.*")
  )
}

/**
 * Holds if untrusted input flows from `source` to `sink` and the sink may execute without
 * protection in `context`.
 */
predicate codeInjectionInContext(
  CodeInjectionFlow::PathNode source, CodeInjectionFlow::PathNode sink,
  WorkflowExecutionContext context
) {
  CodeInjectionFlow::flowPath(source, sink) and
  source.getNode().(RemoteFlowSource).isUntrustedIn(context) and
  context.mayExecute(sink.getNode().asExpr()) and
  sinkMayExecuteForEvent(sink.getNode(), context.getEvent()) and
  not exists(ControlCheck check |
    controlProtectsCodeInjection(check, source.getNode().(RemoteFlowSource), sink.getNode(), context)
  ) and
  not isGithubScriptUsingToJson(sink.getNode().asExpr())
}

/** Holds if a code-injection flow has no concrete trigger context to correlate. */
private predicate codeInjectionWithoutKnownContext(
  CodeInjectionFlow::PathNode source, CodeInjectionFlow::PathNode sink
) {
  CodeInjectionFlow::flowPath(source, sink) and
  not exists(sink.getNode().asExpr().getEnclosingJob().getATriggerEvent()) and
  not isGithubScriptUsingToJson(sink.getNode().asExpr())
}

/**
 * Holds if there is a code injection flow from `source` to `sink` with
 * critical severity, linked by `event`.
 */
predicate criticalSeverityCodeInjection(
  CodeInjectionFlow::PathNode source, CodeInjectionFlow::PathNode sink, Event event
) {
  exists(WorkflowExecutionContext context |
    codeInjectionInContext(source, sink, context) and
    context = getRelevantCriticalContextForSink(sink.getNode()) and
    event = context.getEvent()
  )
}

/**
 * Holds if there is a code injection flow from `source` to `sink` with medium severity.
 */
predicate mediumSeverityCodeInjection(
  CodeInjectionFlow::PathNode source, CodeInjectionFlow::PathNode sink
) {
  not isJobContainerImageSink(sink.getNode()) and
  (
    exists(WorkflowExecutionContext context |
      codeInjectionInContext(source, sink, context) and not context.isPullRequest()
    )
    or
    codeInjectionWithoutKnownContext(source, sink)
  ) and
  not criticalSeverityCodeInjection(source, sink, _)
}

/**
 * Holds if there is a code injection flow from `source` to `sink` exclusively in an isolated
 * `pull_request` context, linked by `event`.
 */
predicate lowSeverityCodeInjection(
  CodeInjectionFlow::PathNode source, CodeInjectionFlow::PathNode sink, Event event
) {
  not isJobContainerImageSink(sink.getNode()) and
  exists(WorkflowExecutionContext context |
    codeInjectionInContext(source, sink, context) and
    context.isPullRequest() and
    event = context.getEvent()
  ) and
  not criticalSeverityCodeInjection(source, sink, _) and
  not mediumSeverityCodeInjection(source, sink)
}

/**
 * Holds if `expr` is the `script` input to `actions/github-script` and it uses
 * `toJson`.
 */
predicate isGithubScriptUsingToJson(Expression expr) {
  exists(UsesStep script |
    script.getCallee() = "actions/github-script" and
    script.getArgumentExpr("script") = expr and
    exists(getAToJsonReferenceExpression(expr.getExpression(), _))
  )
}
