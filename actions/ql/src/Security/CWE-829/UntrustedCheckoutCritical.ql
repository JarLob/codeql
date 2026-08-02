/**
 * @name Checkout of untrusted code in a privileged context
 * @description Privileged workflows have read/write access to the base repository and access to secrets.
 *              By explicitly checking out and running the build script from a fork the untrusted code is running in an environment
 *              that is able to push to the base repository and to access secrets.
 * @kind path-problem
 * @problem.severity error
 * @precision very-high
 * @security-severity 9.3
 * @id actions/untrusted-checkout/critical
 * @tags actions
 *       security
 *       external/cwe/cwe-829
 */

import actions
import codeql.actions.security.UntrustedCheckoutQuery
import codeql.actions.security.PoisonableSteps

query predicate edges(AstNode predecessor, AstNode successor) {
  exists(Step previous, Step next |
    predecessor = previous and
    successor = next and
    previous.getNextStep() = next
  )
  or
  checkoutReferenceEdge(predecessor, successor)
}

from
  PRHeadCheckoutStep checkout, PoisonableStep poisonable, Event event, AstNode checkoutReference,
  string checkoutReferenceText
where
  checkoutReference = getCheckoutReference(checkout) and
  checkoutReferenceText = getCheckoutReferenceText(checkoutReference) and
  criticalSeverityUntrustedCheckout(checkout, poisonable, event)
select checkout, checkoutReference, poisonable,
  "Checkout of untrusted code from $@ in a privileged workflow with later potential execution (event trigger: $@).",
  checkoutReference, checkoutReferenceText, event, event.getName()
