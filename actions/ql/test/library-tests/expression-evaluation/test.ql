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
