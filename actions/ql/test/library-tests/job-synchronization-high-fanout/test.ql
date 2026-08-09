import codeql.actions.JobSynchronization

query predicate execution(string job) {
  exists(Job candidate, Event event |
    candidate.getId() = "high-fanout" and
    event.getName() = "push" and
    jobMayExecuteForEvent(candidate, event) and
    job = candidate.getId()
  )
}

query predicate completion(string job, string status) {
  exists(Job candidate, Event event, JobStatus completionStatus |
    candidate.getId() = "high-fanout" and
    event.getName() = "push" and
    jobMayCompleteForEvent(candidate, event, completionStatus) and
    job = candidate.getId() and
    status = completionStatus.getName()
  )
}

query predicate impossibleCorrelatedExecution(string job) {
  exists(Job candidate, Event event |
    candidate.getId() =
      ["impossible-correlated-fanout", "impossible-aggregate-correlation"] and
    event.getName() = "push" and
    jobMayExecuteForEvent(candidate, event) and
    job = candidate.getId()
  )
}

query predicate requiredSuccessfulCompletion(string job, string needed) {
  exists(Job candidate, Job prerequisite, Event event |
    (
      candidate.getId() = "high-fanout" and prerequisite.getId() = "root-0"
      or
      candidate.getId() = "deep-fanout" and prerequisite.getId() = "chain-0"
    ) and
    event.getName() = "push" and
    jobExecutionRequiresSuccessfulCompletionOf(candidate, prerequisite, event) and
    job = candidate.getId() and
    needed = prerequisite.getId()
  )
}
