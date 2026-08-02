import codeql.actions.security.ControlChecks
import codeql.actions.config.Config

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
        "explicit-failure-dependent", "output-protected-dependent",
        "output-bypassable-dependent"
      ] and
    event.getName() = "pull_request_target" and
    check.protects(sink, event, "untrusted-checkout")
  )
}

query predicate actionChecks(string stepId, string kind) {
  exists(UsesStep step |
    step.getId() = stepId and
    (
      kind = "association" and step instanceof AssociationActionCheck
      or
      kind = "permission" and step instanceof PermissionActionCheck
    )
  )
}

query predicate commentDateChecks(string stepId) {
  exists(BashCommentVsHeadDateCheck check | check.getId() = stepId)
}

query predicate actionControlBehaviors(string action, string version, string capability) {
  action = "actions-cool/check-user-permission" and
  capability = "error-if-missing" and
  version =
    [
      "v2.2.1", "v2.3.0-beta.1", "v2.3.0", "2.3.0", "v2.3.1", "v2.4.0", "v2.9.0",
      "v3.0.0", "v10.0.0", "7b90a27f92f3961b368376107661682c441f6103",
      "c21884f3dda18dafc2f8b402fe807ccc9ec1aa5e", "v2", "v2.x", "main", "master"
    ] and
  actionsControlBehaviorDataModel(action, version, capability)
}
