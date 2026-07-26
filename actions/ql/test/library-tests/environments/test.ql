import codeql.actions.Ast
import codeql.actions.security.ControlChecks

query predicate names(string jobId, string name) {
  exists(Job job |
    job.getId() = jobId and
    name = job.getEnvironment().getName()
  )
}

query predicate urls(string jobId, string url) {
  exists(Job job |
    job.getId() = jobId and
    url = job.getEnvironment().getUrl()
  )
}

query predicate deploymentValues(string jobId, string value) {
  exists(Job job |
    job.getId() = jobId and
    value = job.getEnvironment().getDeploymentValue()
  )
}

query predicate nameExpressions(string jobId, string expression) {
  exists(Job job |
    job.getId() = jobId and
    expression = job.getEnvironment().getNameExpr().getExpression()
  )
}

query predicate urlExpressions(string jobId, string expression) {
  exists(Job job |
    job.getId() = jobId and
    expression = job.getEnvironment().getUrlExpr().getExpression()
  )
}

query predicate deploymentExpressions(string jobId, string expression) {
  exists(Job job |
    job.getId() = jobId and
    expression = job.getEnvironment().getDeploymentExpr().getExpression()
  )
}

query predicate controls(string jobId) {
  exists(Job job, EnvironmentCheck check |
    job.getId() = jobId and
    check = job.getEnvironment()
  )
}