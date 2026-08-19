import codeql.actions.security.UntrustedCheckoutQuery
import codeql.actions.ExpressionEvaluation

from PRHeadCheckoutStep checkout, Event event
where
  checkout.getATriggerEvent() = event and
  checkoutReferenceMayBeNonEmptyForEvent(checkout, event)
select checkout.getEnclosingJob().getId(), event.getName()

query predicate nonEmptyRefValues(string job, string eventName) {
  exists(UsesStep checkout, Event event |
    job = checkout.getEnclosingJob().getId() and
    job = ["repository-empty", "repository-false", "repository-zero"] and
    checkout.getATriggerEvent() = event and
    eventName = event.getName() and
    mayEvaluateToNonEmptyString(checkout.getArgumentExpr("ref").getRoot(), event)
  )
}

query predicate preferredSelectors(string job, string eventName, string selector) {
  exists(PRHeadCheckoutStep checkout, Event event, Expression expression |
    job = checkout.getEnclosingJob().getId() and
    job = "both-selectors" and
    checkout.getATriggerEvent() = event and
    eventName = event.getName() and
    expression = getAFeasibleCheckoutReference(checkout, event) and
    selector = expression.toString()
  )
}
