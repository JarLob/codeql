import codeql.actions.Ast
import codeql.actions.DataFlow
import codeql.actions.TaintTracking

private module SecretBoundaryConfig implements DataFlow::ConfigSig {
  predicate isSource(DataFlow::Node source) {
    exists(ExternalJob caller |
      source.asExpr() = caller.getArgumentExpr("token") or
      source.asExpr() = caller.getSecretExpr("token")
    )
  }

  predicate isSink(DataFlow::Node sink) {
    exists(ReusableWorkflow workflow |
      workflow.getASecretExpr() = sink.asExpr()
      or
      sink.asExpr().(InputsExpression).getTarget() = workflow.getInput("token")
    )
  }

  predicate observeDiffInformedIncrementalMode() { any() }
}

module SecretBoundaryFlow = TaintTracking::Global<SecretBoundaryConfig>;

query predicate declaredSecrets(string secret, string requirement) {
  exists(ReusableWorkflow workflow |
    workflow.getASecretName() = secret and
    if workflow.isSecretRequired(secret)
    then requirement = "required"
    else requirement = "optional"
  )
}

query predicate mappedSecrets(string job, string secret, string value) {
  exists(ExternalJob caller |
    caller.getId() = job and caller.getSecret(secret) = value
  )
}

query predicate inheritedSecretJobs(ExternalJob caller) {
  caller.inheritsSecrets() and caller.isPrivileged()
}

query predicate boundaryFlows(DataFlow::Node source, DataFlow::Node sink) {
  SecretBoundaryFlow::flow(source, sink)
}