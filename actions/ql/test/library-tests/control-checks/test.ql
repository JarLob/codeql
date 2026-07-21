import codeql.actions.security.ControlChecks

query predicate labelChecks(LabelIfCheck check) { any() }

query predicate parsedChecks(ControlCheck check) {
  exists(string event |
    check instanceof If and
    exists(check.(If).getConditionExpr().getRoot()) and
    event = check.getATriggerEvent().getName() and
    check.protectsCategoryAndEvent("untrusted-checkout", event)
  )
}
