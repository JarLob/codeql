import actions
private import codeql.actions.TaintTracking
import codeql.actions.DataFlow
import codeql.actions.dataflow.FlowSources
import codeql.actions.security.ArtifactDownloadSteps
import codeql.actions.security.PoisonableSteps
import codeql.actions.security.UntrustedCheckoutQuery
import codeql.actions.security.ControlChecks
private import codeql.actions.IntegratedExpressionControlFlow as IntegratedCfg

class GitHubCurrentWorkflowDownloadArtifactActionStep extends UntrustedArtifactDownloadStep,
  UsesStep
{
  GitHubCurrentWorkflowDownloadArtifactActionStep() {
    this.getCallee() = "actions/download-artifact" and
    exists(LocalJob job, SimplePRHeadCheckoutStep checkout, UsesStep upload |
      this.getEnclosingWorkflow().getAJob() = job and
      job.getAContainedStep() = checkout and
      checkout.getATriggerEvent().getName() = "pull_request_target" and
      checkout.getAFollowingStep() = upload and
      IntegratedCfg::orderedStepsMayReachForAnyEvent(checkout, upload) and
      upload.getCallee() = "actions/upload-artifact"
    )
  }

  override string getPath() {
    if exists(this.getArgument("path"))
    then result = normalizePath(this.getArgument("path"))
    else result = "GITHUB_WORKSPACE/"
  }
}

/**
 * Compatibility class for GitHub artifact downloads from workflow runs or the current workflow.
 *
 * New code should use `GitHubWorkflowRunDownloadArtifactActionStep` or
 * `GitHubCurrentWorkflowDownloadArtifactActionStep` instead.
 */
deprecated class GitHubDownloadArtifactActionStep extends UntrustedArtifactDownloadStep, UsesStep {
  GitHubDownloadArtifactActionStep() {
    this instanceof GitHubWorkflowRunDownloadArtifactActionStep or
    this instanceof GitHubCurrentWorkflowDownloadArtifactActionStep
  }

  override string getPath() {
    result = this.(GitHubWorkflowRunDownloadArtifactActionStep).getPath()
    or
    result = this.(GitHubCurrentWorkflowDownloadArtifactActionStep).getPath()
  }
}

class ArtifactPoisoningSink extends DataFlow::Node {
  UntrustedArtifactDownloadStep download;

  ArtifactPoisoningSink() {
    exists(PoisonableStep poisonable |
      download.getAFollowingStep() = poisonable and
      IntegratedCfg::orderedStepsMayReachForAnyEvent(download, poisonable) and
      // excluding artifacts downloaded to the temporary directory
      not download.getPath().regexpMatch("^/tmp.*") and
      not download.getPath().regexpMatch("^\\$\\{\\{\\s*runner\\.temp\\s*}}.*") and
      not download.getPath().regexpMatch("^\\$RUNNER_TEMP.*")
    |
      poisonable.(Run).getScript() = this.asExpr() and
      (
        // Check if the poisonable step is a local script execution step
        // and the path of the command or script matches the path of the downloaded artifact
        isSubpath(poisonable.(LocalScriptExecutionRunStep).getPath(), download.getPath())
        or
        // Checking the path for non local script execution steps is very difficult
        not poisonable instanceof LocalScriptExecutionRunStep
        // Its not easy to extract the path from a non-local script execution step so skipping this check for now
        // and isSubpath(poisonable.(Run).getWorkingDirectory(), download.getPath())
      )
      or
      poisonable.(UsesStep) = this.asExpr() and
      (
        not poisonable instanceof LocalActionUsesStep and
        download.getPath() = "GITHUB_WORKSPACE/"
        or
        isSubpath(poisonable.(LocalActionUsesStep).getPath(), download.getPath())
      )
    )
  }

  string getPath() { result = download.getPath() }
}

/**
 * Gets a relevant execution context for the given node in artifact poisoning.
 *
 * This is used to correlate the untrusted source with the privileged sink.
 */
WorkflowExecutionContext getRelevantContextInPrivilegedContext(DataFlow::Node node) {
  result = getAPrivilegedWorkflowExecutionContext(node.asExpr()) and
  not exists(ControlCheck check |
    check.protects(node.asExpr(), result.getEvent(), "artifact-poisoning")
  )
}

/** Gets the event for a relevant artifact-poisoning context. */
Event getRelevantEventInPrivilegedContext(DataFlow::Node node) {
  result = getRelevantContextInPrivilegedContext(node).getEvent()
}

bindingset[sink, event]
pragma[inline_late]
predicate sinkMayExecuteForEvent(DataFlow::Node sink, Event event) {
  IntegratedCfg::mayExecuteForEvent(sink.asExpr(), event)
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
bindingset[source, sink]
pragma[inline_late]
predicate sourceMayReachOnlyNonPrivilegedContext(DataFlow::Node source, DataFlow::Node sink) {
  not exists(sink.asExpr().getEnclosingJob().getATriggerEvent())
  or
  exists(WorkflowExecutionContext context |
    source.(ArtifactSource).isUntrustedIn(context) and
    context.mayExecute(sink.asExpr()) and
    not context.isPullRequest()
  ) and
  not exists(WorkflowExecutionContext context |
    source.(ArtifactSource).isUntrustedIn(context) and context.isPrivileged(sink.asExpr())
  )
}

/**
 * A taint-tracking configuration for unsafe artifacts
 * that is used may lead to artifact poisoning
 */
private module ArtifactPoisoningConfig implements DataFlow::ConfigSig {
  predicate isSource(DataFlow::Node source) { source instanceof ArtifactSource }

  predicate isSink(DataFlow::Node sink) { sink instanceof ArtifactPoisoningSink }

  predicate isAdditionalFlowStep(DataFlow::Node pred, DataFlow::Node succ) {
    exists(PoisonableStep step |
      pred instanceof ArtifactSource and
      pred.asExpr().(Step).getAFollowingStep() = step and
      (
        succ.asExpr() = step.(Run).getScript() or
        succ.asExpr() = step.(UsesStep)
      )
    )
    or
    exists(Run run |
      pred instanceof ArtifactSource and
      pred.asExpr().(Step).getAFollowingStep() = run and
      succ.asExpr() = run.getScript() and
      exists(run.getScript().getAFileReadCommand())
    )
  }

  predicate observeDiffInformedIncrementalMode() { any() }

  Location getASelectedSinkLocation(DataFlow::Node sink) {
    result = sink.getLocation()
    or
    result = getRelevantEventInPrivilegedContext(sink).getLocation()
  }
}

/** Tracks flow of unsafe artifacts that is used in an insecure way. */
module ArtifactPoisoningFlow = TaintTracking::Global<ArtifactPoisoningConfig>;
