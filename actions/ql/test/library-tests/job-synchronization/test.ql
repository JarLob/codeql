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
        "terminal"
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
