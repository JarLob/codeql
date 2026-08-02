import actions
import codeql.actions.security.UntrustedCheckoutQuery

query predicate classifications(string workflow, string job, string category) {
  exists(PRHeadCheckoutStep checkout, Event event |
    workflow = checkout.getLocation().getFile().getBaseName() and
    job = checkout.getEnclosingJob().getId() and
    category = getCheckoutSecurityClassification(checkout, event)
  )
}

query predicate overlappingClassifications(
  string workflow, string job, string leftCategory, string rightCategory
) {
  exists(PRHeadCheckoutStep checkout, Event event |
    workflow = checkout.getLocation().getFile().getBaseName() and
    job = checkout.getEnclosingJob().getId() and
    leftCategory = getCheckoutSecurityClassification(checkout, event) and
    rightCategory = getCheckoutSecurityClassification(checkout, event) and
    leftCategory < rightCategory
  )
}

query predicate unclassifiedCheckouts(string workflow, string job) {
  exists(PRHeadCheckoutStep checkout, Event event |
    checkout.getATriggerEvent() = event and
    event.getName() = checkoutTriggers() and
    workflow = checkout.getLocation().getFile().getBaseName() and
    job = checkout.getEnclosingJob().getId() and
    not exists(getCheckoutSecurityClassification(checkout, event))
  )
}