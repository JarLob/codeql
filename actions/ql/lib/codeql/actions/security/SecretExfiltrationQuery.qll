private import actions
private import codeql.actions.TaintTracking
private import codeql.actions.dataflow.ExternalFlow
import codeql.actions.dataflow.FlowSources
import codeql.actions.DataFlow

private predicate isDirectWholeValueAccess(Expression expression) {
  expression.getParentNode().(ScalarValue).getValue().trim() = expression.getRawExpression().trim() and
  expression.getRoot().getChild(0) instanceof AccessExpression
}

private predicate isTrustedAssociationLiteral(ExpressionNode node) {
  node instanceof LiteralExpression and
  node.(LiteralExpression).getKind() = "StringLiteral" and
  node.(LiteralExpression).getValue().toUpperCase() =
    ["'MEMBER'", "\"MEMBER\"", "'OWNER'", "\"OWNER\""]
}

private predicate isAuthorAssociationAccess(ExpressionNode node) {
  node instanceof AccessExpression and
  node.(AccessExpression).getAccessPath() =
    [
      "github.event.comment.author_association", "github.event.issue.author_association",
      "github.event.pull_request.author_association"
    ]
}

private predicate jobRequiresTrustedAssociation(LocalJob job) {
  exists(If condition, BinaryExpression comparison |
    job.getIf() = condition and
    comparison = condition.getConditionExpr().getRoot().getChild(0) and
    comparison.getOperator() = "==" and
    (
      isAuthorAssociationAccess(comparison.getLeftOperand()) and
      isTrustedAssociationLiteral(comparison.getRightOperand())
      or
      isTrustedAssociationLiteral(comparison.getLeftOperand()) and
      isAuthorAssociationAccess(comparison.getRightOperand())
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
