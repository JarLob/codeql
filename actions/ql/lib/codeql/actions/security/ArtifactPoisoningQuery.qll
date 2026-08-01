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
 * Gets the event that is relevant for the given node in the context of artifact poisoning.
 *
 * This is used to highlight the event in the query results when an alert is raised.
 */
Event getRelevantEventInPrivilegedContext(DataFlow::Node node) {
  inPrivilegedContext(node.asExpr(), result) and
  not exists(ControlCheck check | check.protects(node.asExpr(), result, "artifact-poisoning"))
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
        job.getATriggerEvent() = event and sinkMayExecuteForEvent(sink, event)
      ) and
      not exists(Event event |
        job.getATriggerEvent() = event and
        sinkMayExecuteForEvent(sink, event) and
        job.isPrivilegedExternallyTriggerable(event)
      )
    )
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
