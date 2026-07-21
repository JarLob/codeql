import codeql.actions.ExpressionEvaluation

query predicate knownValues(If condition, Event event, boolean value) {
  condition.getEnclosingWorkflow() = event.getEnclosingWorkflow() and
  evaluatesToBoolean(condition.getConditionExpr().getRoot(), event, value)
}

query predicate feasibleConditions(If condition, Event event) {
  condition.getEnclosingWorkflow() = event.getEnclosingWorkflow() and
  isConditionFeasible(condition, event)
}

query predicate literalSubexpressionValues(ExpressionNode node, boolean value) {
  node.getExpression().getEnclosingJob().getId() = "literals" and
  exists(Event event |
    event = node.getExpression().getEnclosingWorkflow().getOn().getAnEvent() and
    event.getName() = "pull_request" and
    evaluatesToBoolean(node, event, value)
  )
}

query predicate skippedNeedsFeasibleConditions(If condition, Event event) {
  condition.getEnclosingWorkflow() = event.getEnclosingWorkflow() and
  condition.getEnclosingJob().getId() =
    ["always", "success-status", "success-or-event", "not-success-status"] and
  isConditionFeasibleAfterSkippedNeeds(condition, event)
}

query predicate statusCheckConditions(If condition) { hasStatusCheckFunction(condition) }

query predicate knownNeedsStatusValues(string job, string status, boolean value) {
  exists(If condition, Event event |
    job = condition.getEnclosingJob().getId() and
    job = ["success-status", "not-success-status", "failure-status", "cancelled-status"] and
    event = condition.getEnclosingWorkflow().getOn().getAnEvent() and
    event.getName() = "pull_request" and
    status = ["success", "failure", "cancelled", "skipped"] and
    evaluatesToBooleanAfterNeedsStatus(condition.getConditionExpr().getRoot(), event, status, value)
  )
}

query predicate knownNeedsStateValues(
  string job, boolean hasFailure, boolean hasCancellation, boolean hasSkip, boolean value
) {
  exists(If condition, Event event |
    job = condition.getEnclosingJob().getId() and
    job = ["failure-status", "cancelled-status", "combined-status"] and
    event = condition.getEnclosingWorkflow().getOn().getAnEvent() and
    event.getName() = "pull_request" and
    hasFailure in [false, true] and
    hasCancellation in [false, true] and
    hasSkip in [false, true] and
    evaluatesToBooleanAfterNeedsState(condition.getConditionExpr().getRoot(), event, hasFailure,
      hasCancellation, hasSkip, value)
  )
}
