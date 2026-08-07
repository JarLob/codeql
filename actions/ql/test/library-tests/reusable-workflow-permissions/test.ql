import codeql.actions.Ast
import codeql.actions.WorkflowRunSourceEvaluation as ExecutionContexts

private string selectedScope() {
  result =
    [
      "actions", "contents", "security-events", "id-token", "models", "vulnerability-alerts",
      "drives", "copilot-requests"
    ]
}

query predicate effectivePermissions(string workflow, string jobId, string scope, string permission) {
  exists(Job job |
    workflow = job.getLocation().getFile().getBaseName() and
    jobId = job.getId() and
    scope = selectedScope() and
    permission = job.getEffectivePermission(scope)
  )
}

query predicate privilegedJobs(string workflow, string jobId) {
  exists(Job job |
    workflow = job.getLocation().getFile().getBaseName() and
    jobId = job.getId() and
    job.isPrivileged()
  )
}

query predicate compositeActionPrivilege(string action, string privilege) {
  exists(CompositeAction composite |
    action = composite.getLocation().getFile().getRelativePath() and
    if composite.isPrivileged() then privilege = "privileged" else privilege = "unprivileged"
  )
}

query predicate eventPrivilege(string workflow, string jobId, string event, string privilege) {
  exists(Job job, Event trigger |
    workflow = job.getLocation().getFile().getBaseName() and
    jobId = job.getId() and
    job.getATriggerEvent() = trigger and
    event = trigger.getName() and
    if ExecutionContexts::getAPrivilegedWorkflowExecutionContext(job).getEvent() = trigger
    then privilege = "privileged"
    else privilege = "unprivileged"
  )
}
