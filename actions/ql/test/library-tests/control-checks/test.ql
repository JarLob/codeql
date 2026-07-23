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

query predicate neededJobProtection(string protectedJob) {
  exists(ControlCheck check, Step sink, Event event |
    check.getEnclosingJob().getId() = "needed-label-check" and
    protectedJob = sink.getEnclosingJob().getId() and
    protectedJob =
      [
        "protected-dependent", "bypassable-dependent", "explicit-success-dependent",
        "explicit-failure-dependent"
      ] and
    event.getName() = "pull_request_target" and
    check.protects(sink, event, "untrusted-checkout")
  )
}
