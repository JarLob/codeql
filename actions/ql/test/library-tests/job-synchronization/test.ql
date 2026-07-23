import codeql.actions.JobSynchronization

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
        "named-results", "unknown-named-result", "output-default-dependent",
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
    step.getId() = ["step-continue-true", "step-continue-false", "step-continue-dynamic"] and
    scope = "step" and
    id = step.getId() and
    outcome = failure.getName() and
    conclusion = getAStepConclusionForOutcome(step, event, failure).getName()
  )
}

query predicate continueOnErrorCompletionStatuses(string job, string status) {
  exists(JobCompletionNode completion |
    completion.getJob().getId() = ["continue-true", "continue-false", "continue-dynamic"] and
    job = completion.getJob().getId() and
    status = completion.getStatus().getName()
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
