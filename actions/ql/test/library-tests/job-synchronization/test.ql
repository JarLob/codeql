import codeql.actions.JobSynchronization
import codeql.actions.DataFlow
import codeql.actions.TaintTracking

private module MatrixReusableFlowConfig implements DataFlow::ConfigSig {
  predicate isSource(DataFlow::Node source) {
    exists(ExternalJob caller |
      caller.getId() = "matrix-call-reusable" and
      (
        exists(string inputName |
          inputName = ["target", "active", "retries"] and
          source.asExpr() = caller.getArgumentExpr(inputName)
        )
        or
        source.asExpr() = caller.getSecretExpr("token")
      )
    )
  }

  predicate isSink(DataFlow::Node sink) {
    exists(ReusableWorkflow workflow |
      workflow.getACaller().getId() = "matrix-call-reusable" and
      (
        exists(string inputName |
          inputName = ["target", "active", "retries"] and
          sink.asExpr().(InputsExpression).getTarget() = workflow.getInput(inputName)
        )
        or
        workflow.getASecretExpr() = sink.asExpr()
      )
    )
  }

  predicate observeDiffInformedIncrementalMode() { any() }
}

private module MatrixReusableFlow = TaintTracking::Global<MatrixReusableFlowConfig>;

query predicate joinRequirements(string job, string requiredJob) {
  exists(NeedsJoinNode join |
    job = join.getJob().getId() and requiredJob = join.getARequiredJob().getId()
  )
}

query predicate joinRequirementCompletions(string job, string requiredJob, string status) {
  exists(NeedsJoinNode join, JobCompletionNode completion |
    completion = join.getARequiredCompletion() and
    job = join.getJob().getId() and
    requiredJob = completion.getJob().getId() and
    status = completion.getStatus().getName()
  )
}

query predicate joinDecisionStatuses(string job, string status) {
  exists(NeedsJoinNode join, JobDecisionNode decision |
    decision = join.getASuccessor() and
    job = join.getJob().getId() and
    status = decision.getNeedsStatus().getName()
  )
}

query predicate decisionEdges(string job, string successor) {
  exists(JobDecisionNode decision |
    job = decision.getJob().getId() and successor = decision.getASuccessor().toString()
  )
}

query predicate pushDecisionEdges(string job, string successor) {
  exists(JobDecisionNode decision, Event event |
    event = decision.getJob().getEnclosingWorkflow().getOn().getAnEvent() and
    event.getName() = "push" and
    job = decision.getJob().getId() and
    successor = decision.getASuccessor(event).toString()
  )
}

query predicate knownStatusDecisionEdges(string job, string status, string successor) {
  exists(JobDecisionNode decision, Event event |
    event = decision.getJob().getEnclosingWorkflow().getOn().getAnEvent() and
    event.getName() = "push" and
    job = decision.getJob().getId() and
    job =
      [
        "dependent", "always-dependent", "success-dependent", "failure-dependent",
        "cancelled-dependent", "not-success-dependent", "combined-dependent", "transitive-combined",
        "named-results", "unknown-named-result", "after-reusable", "after-reusable-blocked",
        "after-reusable-direct", "after-reusable-dynamic", "after-nested-reusable",
        "output-default-dependent",
        "output-always-dependent", "output-blocked-dependent", "output-dynamic-dependent",
        "terminal", "output-empty-dependent", "output-boolean-dependent", "output-skipped-dependent",
        "continue-true-success-dependent", "continue-true-failure-dependent",
        "continue-dynamic-result-dependent", "matrix-output-enabled", "matrix-output-blocked",
        "matrix-output-dynamic", "output-negated-dependent", "output-failure-dependent"
      ] and
    status = decision.getNeedsStatus().getName() and
    successor = decision.getASuccessor(event).toString()
  )
}

query predicate executionCompletions(string job, string status) {
  exists(JobExecutionNode execution, JobCompletionNode completion |
    completion = execution.getASuccessor() and
    job = execution.getJob().getId() and
    status = completion.getStatus().getName()
  )
}

query predicate executionCfgNodes(string job, Job cfgJob) {
  exists(JobExecutionNode execution |
    job = execution.getJob().getId() and cfgJob = execution.getCfgNode().getAstNode()
  )
}

query predicate matrixExecutions(string job, string instance) {
  exists(MatrixJobExecutionNode execution |
    job = execution.getJob().getId() and instance = execution.getInstance().toString()
  )
}

query predicate matrixProjectedValues(
  string job, string instance, string key, string value
) {
  exists(MatrixJobInstance matrixInstance |
    matrixInstance.getJob().getId() =
      [
        "matrix-exclude", "matrix-include", "matrix-include-only", "matrix-empty-include"
      ] and
    job = matrixInstance.getJob().getId() and
    instance = matrixInstance.toString() and
    key = matrixInstance.getAMatrixKey() and
    value = matrixInstance.getMatrixValue(key)
  )
}

query predicate matrixFanInRequirements(string job, string requiredJob, string status) {
  exists(NeedsJoinNode join, MatrixJobFanInNode fanIn |
    fanIn = join.getARequiredMatrixFanIn() and
    job = join.getJob().getId() and
    requiredJob = fanIn.getJob().getId() and
    status = fanIn.getStatus().getName()
  )
}

query predicate continueOnErrorTransformations(
  string scope, string id, string outcome, string conclusion
) {
  exists(Job job, Event event, FailureStatus failure |
    event = job.getEnclosingWorkflow().getOn().getAnEvent() and
    event.getName() = "push" and
    job.getId() = ["continue-true", "continue-false", "continue-dynamic"] and
    scope = "job" and
    id = job.getId() and
    outcome = failure.getName() and
    conclusion = getAJobConclusionForOutcome(job, event, failure).getName()
  )
  or
  exists(Step step, Event event, FailureStatus failure |
    event = step.getEnclosingWorkflow().getOn().getAnEvent() and
    event.getName() = "push" and
    step.getId() =
      [
        "step-continue-true", "step-continue-false", "step-continue-dynamic",
        "step-continue-only"
      ] and
    scope = "step" and
    id = step.getId() and
    outcome = failure.getName() and
    conclusion = getAStepConclusionForOutcome(step, event, failure).getName()
  )
}

query predicate continueOnErrorCompletionStatuses(string job, string status) {
  exists(JobCompletionNode completion |
    completion.getJob().getId() =
      ["continue-true", "continue-false", "continue-dynamic", "step-continue-only"] and
    job = completion.getJob().getId() and
    status = completion.getStatus().getName()
  )
}

query predicate eventCompletionStatuses(string job, string status) {
  exists(Job completedJob, Event event, JobStatus completionStatus |
    completedJob.getId() =
      [
        "continue-true", "continue-false", "continue-dynamic", "step-continue-only",
        "matrix-continue-true", "matrix-job-continue-expression",
        "matrix-step-continue-expression"
      ] and
    event.getName() = "push" and
    jobMayCompleteForEvent(completedJob, event, completionStatus) and
    job = completedJob.getId() and
    status = completionStatus.getName()
  )
}

query predicate completionOutcomes(string job, string conclusion, string outcome) {
  exists(JobCompletionNode completion, Event event |
    completion.getJob().getId() =
      ["continue-true", "continue-false", "continue-dynamic", "step-continue-only"] and
    event.getName() = "push" and
    job = completion.getJob().getId() and
    conclusion = completion.getStatus().getName() and
    outcome = completion.getAOutcome(event).getName()
  )
}

query predicate contributingStepOutcomes(
  string job, string step, string conclusion, string outcome
) {
  exists(JobCompletionNode completion, Step completedStep, Event event |
    completion.getJob().getId() =
      ["continue-true", "continue-false", "continue-dynamic", "step-continue-only"] and
    completedStep.getEnclosingJob() = completion.getJob() and
    completedStep.getId() =
      ["step-continue-true", "step-continue-false", "step-continue-dynamic", "step-continue-only"] and
    event.getName() = "push" and
    job = completion.getJob().getId() and
    step = completedStep.getId() and
    conclusion = completion.getStatus().getName() and
    outcome = completion.getAContributingStepOutcome(completedStep, event).getName()
  )
}

query predicate matrixContinueOnErrorTransformations(
  string scope, string instance, string outcome, string conclusion
) {
  exists(MatrixJobInstance matrixInstance, Event event, FailureStatus failure |
    matrixInstance.getJob().getId() =
      [
        "matrix-job-continue-complex", "matrix-job-continue-dynamic",
        "matrix-job-continue-expression", "matrix-job-continue-nested", "matrix-include-only"
      ] and
    event.getName() = "push" and
    scope = "job" and
    instance = matrixInstance.toString() and
    outcome = failure.getName() and
    conclusion =
      getAMatrixJobConclusionForOutcome(matrixInstance, event, failure).getName()
  )
  or
  exists(MatrixJobInstance matrixInstance, Step step, Event event, FailureStatus failure |
    matrixInstance.getJob().getId() =
      ["matrix-job-continue-nested", "matrix-step-continue-expression"] and
    step.getEnclosingJob() = matrixInstance.getJob() and
    step.getId() = ["matrix-step-continue", "matrix-step-continue-nested"] and
    event.getName() = "push" and
    scope = "step" and
    instance = matrixInstance.toString() and
    outcome = failure.getName() and
    conclusion =
      getAMatrixStepConclusionForOutcome(step, matrixInstance, event, failure).getName()
  )
}

query predicate matrixContinueOnErrorCompletionOutcomes(
  string job, string instance, string conclusion, string outcome
) {
  exists(MatrixJobCompletionNode completion, Event event |
    completion.getJob().getId() =
      [
        "matrix-job-continue-complex", "matrix-job-continue-dynamic",
        "matrix-job-continue-expression", "matrix-job-continue-nested",
        "matrix-step-continue-expression", "matrix-include-only"
      ] and
    event.getName() = "push" and
    job = completion.getJob().getId() and
    instance = completion.getInstance().toString() and
    conclusion = completion.getStatus().getName() and
    outcome = completion.getAOutcome(event).getName()
  )
}

query predicate matrixContributingStepOutcomes(
  string job, string instance, string step, string conclusion, string outcome
) {
  exists(MatrixJobCompletionNode completion, Step completedStep, Event event |
    completion.getJob().getId() =
      [
        "matrix-job-continue-expression", "matrix-job-continue-nested",
        "matrix-step-continue-expression"
      ] and
    completedStep.getEnclosingJob() = completion.getJob() and
    event.getName() = "push" and
    job = completion.getJob().getId() and
    instance = completion.getInstance().toString() and
    step = completedStep.getId() and
    conclusion = completion.getStatus().getName() and
    outcome = completion.getAContributingStepOutcome(completedStep, event).getName()
  )
}

query predicate reusableWorkflowBoundaryEdges(string caller, string boundary, string successor) {
  exists(ExternalJob external, ReusableWorkflow callee, JobDecisionNode decision,
    WorkflowEntryNode entry, Event event |
    callee.getACaller() = external and
    decision.getJob() = external and
    entry.getWorkflow() = callee and
    entry = decision.getASuccessor(event) and
    event.getName() = "push" and
    caller = external.getId() and
    boundary = "callee-entry" and
    successor = entry.toString()
  )
  or
  exists(ExternalJob external, ReusableWorkflow callee, WorkflowExitNode exit,
    JobCompletionNode completion |
    callee.getACaller() = external and
    exit.getWorkflow() = callee and
    completion = exit.getASuccessor() and
    completion.getJob() = external and
    caller = external.getId() and
    boundary = "caller-completion" and
    successor = completion.toString()
  )
}

query predicate reusableCallerCompletionStatuses(string caller, string status) {
  exists(ExternalJob external, Event event, JobStatus completionStatus |
    external.getId() = ["call-reusable", "call-nested-reusable"] and
    event.getName() = "push" and
    jobMayCompleteForEvent(external, event, completionStatus) and
    caller = external.getId() and
    status = completionStatus.getName()
  )
}

query predicate matrixReusableWorkflowBoundaryEdges(
  string caller, string instance, string boundary, string successor
) {
  exists(MatrixJobExecutionNode execution, WorkflowEntryNode entry |
    execution.getJob().getId() = "matrix-call-reusable" and
    entry = execution.getASuccessor() and
    caller = execution.getJob().getId() and
    instance = execution.getInstance().toString() and
    boundary = "callee-entry" and
    successor = entry.toString()
  )
  or
  exists(WorkflowExitNode exit, MatrixJobCompletionNode completion |
    completion = exit.getASuccessor() and
    completion.getJob().getId() = "matrix-call-reusable" and
    caller = completion.getJob().getId() and
    instance = completion.getInstance().toString() and
    boundary = "caller-completion" and
    successor = completion.toString()
  )
}

query predicate matrixReusableInstanceCompletionStatuses(string instance, string status) {
  exists(WorkflowExitNode exit, MatrixJobCompletionNode completion |
    completion = exit.getASuccessor() and
    completion.getJob().getId() = "matrix-call-reusable" and
    instance = completion.getInstance().toString() and
    status = completion.getStatus().getName()
  )
}

query predicate matrixReusableCalleeExecutions(
  string instance, string calleeJob, string execution
) {
  exists(MatrixJobExecutionNode callerExecution, WorkflowEntryNode entry,
    JobExecutionNode calleeExecution, Event event |
    callerExecution.getJob().getId() = "matrix-call-reusable" and
    entry = callerExecution.getASuccessor() and
    event.getName() = "push" and
    calleeExecution = entry.getAReachableNode(event) and
    calleeExecution.getJob().getId() = "matrix-reusable-terminal" and
    instance = callerExecution.getInstance().toString() and
    calleeJob = calleeExecution.getJob().getId() and
    execution = calleeExecution.toString()
  )
}

query predicate matrixReusableFanInStatuses(string caller, string status) {
  exists(MatrixJobCompletionNode completion, MatrixJobFanInNode fanIn, Event event |
    fanIn = completion.getASuccessor() and
    fanIn.getJob().getId() = "matrix-call-reusable" and
    event.getName() = "push" and
    jobMayCompleteForEvent(fanIn.getJob(), event, fanIn.getStatus()) and
    caller = fanIn.getJob().getId() and
    status = fanIn.getStatus().getName()
  )
}

query predicate matrixReusableBoundaryFlows(
  string instance, string kind, string value, DataFlow::Node source, DataFlow::Node sink
) {
  exists(MatrixJobInstance matrixInstance, ExternalJob caller |
    matrixInstance.getJob() = caller and
    caller.getId() = "matrix-call-reusable" and
    instance = matrixInstance.toString() and
    (
      exists(string inputName, string accessPath |
        (
          inputName = "target" and accessPath = "platform.target"
          or
          inputName = "active" and accessPath = "platform.active"
          or
          inputName = "retries" and accessPath = "platform.retries"
        ) and
        source.asExpr() = caller.getArgumentExpr(inputName) and
        value = matrixInstance.getMatrixValue(accessPath) and
        sink.asExpr() instanceof InputsExpression and
        kind = "input:" + inputName
      )
      or
      source.asExpr() = caller.getSecretExpr("token") and
      value = "mapped" and
      kind = "secret"
    ) and
    MatrixReusableFlow::flow(source, sink)
  )
}

query predicate matrixReusableOutputValues(string instance, string output, string value) {
  exists(MatrixJobInstance matrixInstance |
    matrixInstance.getJob().getId() = "matrix-call-reusable" and
    output = ["active", "direct", "retries", "selected"] and
    instance = matrixInstance.toString() and
    value = matrixInstance.getReusableWorkflowOutputValue(output)
  )
}

query predicate matrixReusableOutputDecisions(string job, string status, string successor) {
  exists(JobDecisionNode decision, Event event |
    decision.getJob().getId() =
      [
        "after-matrix-reusable", "after-matrix-reusable-selected-alpha",
        "after-matrix-reusable-selected-beta", "after-matrix-reusable-selected-gamma",
        "after-matrix-reusable-active", "after-matrix-reusable-retries-three"
      ] and
    event.getName() = "push" and
    job = decision.getJob().getId() and
    status = decision.getNeedsStatus().getName() and
    successor = decision.getASuccessor(event).toString()
  )
}

query predicate reusableTerminalCompletionStatuses(string job, string status) {
  exists(Job terminal, Event event, JobStatus completionStatus |
    terminal.getId() = ["reusable-terminal", "reusable-skipped-terminal"] and
    event.getName() = "push" and
    jobMayCompleteForEvent(terminal, event, completionStatus) and
    job = terminal.getId() and
    status = completionStatus.getName()
  )
}

query predicate workflowBoundaries(string boundary, string job) {
  exists(WorkflowEntryNode entry, JobDecisionNode decision |
    decision = entry.getASuccessor() and boundary = "entry" and job = decision.getJob().getId()
  )
  or
  exists(WorkflowExitNode exit, JobCompletionNode completion |
    completion = exit.getAPredecessor() and
    boundary = "exit" and
    job = completion.getJob().getId()
  )
}

query predicate synchronizationCycles(Node node) { node.getASuccessor+() = node }

query predicate impossibleStatusSummaries(string job, string status) {
  exists(JobDecisionNode decision |
    decision.getNeedsStatus().getNonSuccessKindCount() > count(decision.getJob().getANeededJob+()) and
    job = decision.getJob().getId() and
    status = decision.getNeedsStatus().getName()
  )
}

query predicate requiredSuccessfulJobs(string job, string requiredJob) {
  exists(Job dependent, Job required, Event event |
    dependent.getId() = job and
    required.getId() = requiredJob and
    event = dependent.getEnclosingWorkflow().getOn().getAnEvent() and
    event.getName() = "push" and
    jobExecutionRequiresSuccessfulCompletionOf(dependent, required, event)
  )
}

query predicate exactCorrelatedRequiredSuccessfulJobs(string requiredJob) {
  exists(Job dependent, Job required, Event event |
    dependent.getId() = "correlated-dependent" and
    requiredJob = required.getId() and
    event = dependent.getEnclosingWorkflow().getOn().getAnEvent() and
    event.getName() = "push" and
    jobExecutionRequiresSuccessfulCompletionOf(dependent, required, event)
  )
}
