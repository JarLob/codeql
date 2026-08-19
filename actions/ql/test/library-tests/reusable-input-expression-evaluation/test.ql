import codeql.actions.ExpressionEvaluation

private predicate testCondition(If condition, string job) {
  job = condition.getEnclosingJob().getId() and
  job = ["omitted-default", "static", "dynamic", "non-input"]
}

query predicate knownValues(string job, string eventWorkflow, boolean value) {
  exists(If condition, Event event |
    testCondition(condition, job) and
    condition.getEnclosingWorkflow().getATriggerEvent() = event and
    eventWorkflow = event.getEnclosingWorkflow().getLocation().getFile().getRelativePath() and
    evaluatesToBoolean(condition.getConditionExpr().getRoot(), event, value)
  )
}

query predicate possibleValues(string job, string eventWorkflow, boolean value) {
  exists(If condition, Event event |
    testCondition(condition, job) and
    condition.getEnclosingWorkflow().getATriggerEvent() = event and
    eventWorkflow = event.getEnclosingWorkflow().getLocation().getFile().getRelativePath() and
    mayEvaluateToBoolean(condition.getConditionExpr().getRoot(), event, value)
  )
}

query predicate semanticCoverage(string check) {
  exists(If condition, Event event |
    condition.getEnclosingJob().getId() =
      ["contains-input", "starts-with-input", "ends-with-input", "truthy-input",
        "nested-input-boolean"] and
    event.getEnclosingWorkflow().getLocation().getFile().getRelativePath() =
      ".github/workflows/caller.yml" and
    condition.getEnclosingWorkflow().getATriggerEvent() = event and
    evaluatesToBoolean(condition.getConditionExpr().getRoot(), event, true) and
    check = condition.getEnclosingJob().getId()
  )
  or
  exists(ExpressionRoot root, Event event |
    root.getExpression().getEnclosingJob().getId() =
      ["generic-input", "generic-equality", "generic-function", "generic-logical"] and
    not exists(If condition | condition.getConditionExpr() = root.getExpression()) and
    event.getEnclosingWorkflow().getLocation().getFile().getRelativePath() =
      ".github/workflows/caller.yml" and
    root.getExpression().getEnclosingWorkflow().getATriggerEvent() = event and
    evaluatesToBoolean(root, event, true) and
    check = root.getExpression().getEnclosingJob().getId()
  )
}
