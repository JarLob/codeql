private import actions
private import codeql.actions.TaintTracking
private import codeql.actions.dataflow.ExternalFlow
import codeql.actions.dataflow.FlowSources
import codeql.actions.DataFlow
private import codeql.actions.security.ControlCheckConditions as Conditions
private import codeql.actions.ExpressionEvaluation as Evaluation

private predicate isDirectWholeValueAccess(Expression expression) {
  expression.getParentNode().(ScalarValue).getValue().trim() = expression.getRawExpression().trim() and
  expression.getRoot().getChild(0) instanceof AccessExpression
}

private predicate jobRequiresTrustedAssociation(LocalJob job) {
  Conditions::conditionRequiresTrustedAssociation(job.getIf())
}

bindingset[condition, event]
pragma[inline_late]
private predicate conditionMayPermitEvent(If condition, Event event) {
  Evaluation::isConditionFeasible(condition, event)
}

bindingset[job, event]
pragma[inline_late]
private predicate jobConditionMayPermitEvent(LocalJob job, Event event) {
  job.getATriggerEvent() = event and
  (
    not exists(job.getIf())
    or
    exists(If condition |
      condition = job.getIf() and
      (
        not exists(condition.getConditionExpr().getRoot())
        or
        conditionMayPermitEvent(condition, event)
      )
    )
  )
}

private class ContainerRegistryCredentialExfiltrationSink extends DataFlow::Node {
  ContainerRegistryCredentialExfiltrationSink() {
    exists(
      LocalJob job, Expression image, ScalarValue username, SecretsExpression password, Event event
    |
      image = [job.getJobContainerImageExpr(), job.getAServiceContainerImageExpr()] and
      this.asExpr() = image and
      isDirectWholeValueAccess(image) and
      job.getRegistryUsernameForContainerImage(image) = username and
      username.getValue().trim() != "" and
      job.getRegistryPasswordExprForContainerImage(image) = password and
      job.isPrivilegedExternallyTriggerable(event) and
      jobConditionMayPermitEvent(job, event) and
      image.getATriggerEvent() = event and
      not jobRequiresTrustedAssociation(job)
    )
  }
}

private class SecretExfiltrationSink extends DataFlow::Node {
  SecretExfiltrationSink() {
    madSink(this, "secret-exfiltration") or
    this instanceof ContainerRegistryCredentialExfiltrationSink
  }
}

/**
 * A taint-tracking configuration for untrusted data that reaches a sink where it may lead to secret exfiltration
 */
private module SecretExfiltrationConfig implements DataFlow::ConfigSig {
  predicate isSource(DataFlow::Node source) { source instanceof RemoteFlowSource }

  predicate isSink(DataFlow::Node sink) { sink instanceof SecretExfiltrationSink }

  predicate observeDiffInformedIncrementalMode() { any() }
}

/** Tracks flow of unsafe user input that is used in a context where it may lead to a secret exfiltration. */
module SecretExfiltrationFlow = TaintTracking::Global<SecretExfiltrationConfig>;
