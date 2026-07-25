import codeql.actions.IntegratedExpressionControlFlow as IntegratedCfg
import codeql.actions.JobSynchronization

query predicate eventReachability(string job, string source, string target) {
  exists(LocalJob local, Step sourceStep, Step targetStep, Event event |
    local.getId() = "ordered-conditions" and
    job = local.getId() and
    local.getAContainedStep() = sourceStep and
    source = sourceStep.getId() and
    source = "guarded" and
    local.getAContainedStep() = targetStep and
    target = targetStep.getId() and
    target = "after-guarded" and
    event.getName() = "push" and
    IntegratedCfg::mayReachForEvent(sourceStep, targetStep, event)
  )
}

query predicate forbiddenReachability(string description) {
  exists(LocalJob local, Step sourceStep, Step targetStep, Event event |
    local.getId() = "ordered-conditions" and
    local.getAContainedStep() = sourceStep and
    sourceStep.getId() = "guarded" and
    local.getAContainedStep() = targetStep and
    targetStep.getId() = "after-guarded" and
    event.getName() = ["pull_request", "issue_comment", "workflow_run"] and
    IntegratedCfg::mayReachForEvent(sourceStep, targetStep, event) and
    description = "non-push guarded step reaches successor"
  )
}

query predicate fanInExecution(string job) {
  exists(Job candidate, Event event |
    candidate.getId() = ["condition-free-fan-in", "output-gate"] and
    event.getName() = "push" and
    jobMayExecuteForEvent(candidate, event) and
    job = candidate.getId()
  )
}

query predicate matrixCompletion(string job, string status) {
  exists(Job candidate, Event event, JobStatus completion |
    candidate.getId() = ["matrix-static", "matrix-dynamic"] and
    event.getName() = "push" and
    jobMayCompleteForEvent(candidate, event, completion) and
    job = candidate.getId() and
    status = completion.getName()
  )
}

query predicate matrixStepFailureConclusion(string instance, string conclusion) {
  exists(MatrixJobInstance matrixInstance, Step step, Event event, FailureStatus failure |
    matrixInstance.getJob().getId() = "matrix-dynamic" and
    step.getEnclosingJob() = matrixInstance.getJob() and
    step.getId() = "dynamic" and
    event.getName() = "push" and
    instance = matrixInstance.toString() and
    conclusion =
      getAMatrixStepConclusionForOutcome(step, matrixInstance, event, failure).getName()
  )
}


query predicate literalTrueStepFailureConclusion(string instance, string conclusion) {
  exists(MatrixJobInstance matrixInstance, Step step, Event event, FailureStatus failure |
    matrixInstance.getJob().getId() = "matrix-static" and
    step.getEnclosingJob() = matrixInstance.getJob() and
    step.getId() = "static-true" and
    event.getName() = "push" and
    instance = matrixInstance.toString() and
    conclusion =
      getAMatrixStepConclusionForOutcome(step, matrixInstance, event, failure).getName()
  )
}

query predicate matrixCapFallback(string instance) {
  exists(MatrixJobInstance matrixInstance |
    matrixInstance.getJob().getId() = "matrix-capped" and
    matrixInstance.getAssignment() = "*" and
    instance = matrixInstance.toString()
  )
}