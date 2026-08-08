import codeql.actions.IntegratedExpressionControlFlow as IntegratedCfg
import codeql.actions.JobSynchronization
import codeql.actions.security.CodeInjectionSinks

query predicate anchoredStepCount(int total) {
  total =
    count(Step step |
      step.getEnclosingJob().getId().matches("anchor-load-%")
    |
      step
    )
}

query predicate anchoredStructuralSinkCount(int total) {
  total =
    count(CodeInjectionSink sink |
      sink.asExpr().getEnclosingJob().getId().matches("anchor-load-%")
    |
      sink
    )
}

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
    IntegratedCfg::orderedStepsMayReachForEvent(sourceStep, targetStep, event)
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
    IntegratedCfg::orderedStepsMayReachForEvent(sourceStep, targetStep, event) and
    description = "non-push guarded step reaches successor"
  )
}

query predicate fanInExecution(string job) {
  exists(Job candidate, Event event |
    candidate.getId() = ["condition-free-fan-in", "output-gate", "large-fan-in"] and
    event.getName() = "push" and
    jobMayExecuteForEvent(candidate, event) and
    job = candidate.getId()
  )
}

query predicate largeFanInStatusCount(int total) {
  total =
    count(NeedsStatus status |
      exists(JobDecisionNode decision, Event event |
        decision.getJob().getId() = "large-fan-in" and
        event.getName() = "push" and
        decision.getNeedsStatus() = status and
        exists(decision.getASuccessor(event))
      )
    |
      status
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

query predicate stepConditionProjectionIncludesUndemandedAxis(string assignment) {
  exists(MatrixJobInstance matrixInstance |
    matrixInstance.getJob().getId() = "matrix-static" and
    assignment = matrixInstance.getAssignment() and
    assignment.matches("%os=%")
  )
}

query predicate matrixProjectionCount(int instanceCount) {
  instanceCount = count(MatrixJobInstance matrixInstance |
    matrixInstance.getJob().getId() = "matrix-capped"
  )
}

query predicate matrixProjectionIncludesUndemandedAxis(string assignment) {
  exists(MatrixJobInstance matrixInstance |
    matrixInstance.getJob().getId() = "matrix-capped" and
    assignment = matrixInstance.getAssignment() and
    assignment.matches("%second=%")
  )
}

query predicate matrixProjectionFailureConclusions(string conclusion, int instanceCount) {
  exists(Event event, FailureStatus failure |
    event.getName() = "push" and
    conclusion = ["failure", "success"] and
    instanceCount = count(MatrixJobInstance matrixInstance |
      matrixInstance.getJob().getId() = "matrix-capped" and
      getAMatrixJobConclusionForOutcome(matrixInstance, event, failure).getName() = conclusion
    )
  )
}