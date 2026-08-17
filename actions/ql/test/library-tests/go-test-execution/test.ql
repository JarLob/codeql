import actions
import codeql.actions.security.PoisonableSteps
import codeql.actions.security.UntrustedCheckoutQuery

from PRHeadCheckoutStep checkout, PoisonableStep execution, Event event
where checkoutMayLeadToCodeExecution(checkout, execution, event)
select checkout, execution, event
