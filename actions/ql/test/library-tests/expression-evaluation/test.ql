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
  node.getExpression().getEnclosingJob().getId() =
    ["literals", "zero-literal", "nonzero-literal", "empty-string-literal", "null-literal"] and
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

query predicate matrixConditionValues(
  string job, string instance, string step, boolean value
) {
  exists(Step matrixStep, If condition, Event event, MatrixCombination combination |
    condition = matrixStep.getIf() and
    job = condition.getEnclosingJob().getId() and
    job = ["matrix-scalars", "matrix-structured", "matrix-types"] and
    step = matrixStep.getId() and
    combination.getStrategy() = condition.getEnclosingJob().getStrategy() and
    instance = combination.getAssignment() and
    event = condition.getEnclosingWorkflow().getOn().getAnEvent() and
    event.getName() = "pull_request" and
    evaluatesToBooleanForMatrixCombination(condition.getConditionExpr().getRoot(), event,
      combination, value)
  )
}

query predicate matrixConditionMayValues(
  string job, string instance, string step, boolean value
) {
  exists(Step matrixStep, If condition, Event event, MatrixCombination combination |
    condition = matrixStep.getIf() and
    job = condition.getEnclosingJob().getId() and
    job = ["matrix-scalars", "matrix-structured", "matrix-types"] and
    step = matrixStep.getId() and
    combination.getStrategy() = condition.getEnclosingJob().getStrategy() and
    instance = combination.getAssignment() and
    event = condition.getEnclosingWorkflow().getOn().getAnEvent() and
    event.getName() = "pull_request" and
    mayEvaluateConditionToBooleanForMatrixCombination(condition,
      condition.getConditionExpr().getRoot(), event, combination, value)
  )
}

query predicate matrixKnownNeedsStateValues(
  string instance, boolean hasFailure, boolean value
) {
  exists(Step matrixStep, If condition, Event event, MatrixCombination combination |
    matrixStep.getEnclosingJob().getId() = "matrix-scalars" and
    matrixStep.getId() = "status-and-matrix" and
    condition = matrixStep.getIf() and
    combination.getStrategy() = matrixStep.getEnclosingJob().getStrategy() and
    instance = combination.getAssignment() and
    event = condition.getEnclosingWorkflow().getOn().getAnEvent() and
    event.getName() = "pull_request" and
    hasFailure in [false, true] and
    evaluatesToBooleanForMatrixCombinationAfterNeedsState(
      condition.getConditionExpr().getRoot(), event, combination, hasFailure, false, false, value
    )
  )
}

query predicate matrixScalarValues(
  string job, string instance, string accessPath, string kind, string value
) {
  exists(Job matrixJob, MatrixCombination combination |
    job = matrixJob.getId() and
    job = ["matrix-structured", "matrix-types"] and
    combination.getStrategy() = matrixJob.getStrategy() and
    instance = combination.getAssignment() and
    accessPath =
      ["platform.os", "platform.experimental", "nullable", "text"] and
    kind = combination.getValueKind(accessPath) and
    value = combination.getValue(accessPath)
  )
}
