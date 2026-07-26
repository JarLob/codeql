import actions
import codeql.actions.security.ControlCheckConditions as Conditions

query predicate trustedAssociations(string jobId) {
  exists(LocalJob job |
    job.getId() = jobId and
    Conditions::conditionRequiresTrustedAssociation(job.getIf())
  )
}

query predicate parsedOwners(string jobId, string kind) {
  exists(LocalJob job |
    job.getId() = jobId and
    kind = ["association", "label"] and
    Conditions::isParsedCheckOwner(job.getIf(), kind)
  )
}

query predicate protectedConditions(string jobId) {
  exists(LocalJob job, Event event |
    job.getId() = jobId and
    job.getATriggerEvent() = event and
    Conditions::parsedConditionProtectsCategoryAndEvent(job.getIf(), "code-injection",
      event.getName())
  )
}