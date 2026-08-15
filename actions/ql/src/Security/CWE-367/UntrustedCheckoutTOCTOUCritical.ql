/**
 * @name Untrusted Checkout TOCTOU
 * @description Untrusted Checkout is protected by a security check but the checked-out branch can be changed after the check.
 * @kind path-problem
 * @problem.severity error
 * @precision high
 * @security-severity 9.3
 * @id actions/untrusted-checkout-toctou/critical
 * @tags actions
 *       security
 *       external/cwe/cwe-367
 */

import actions
import codeql.actions.security.PoisonableSteps
import codeql.actions.security.UntrustedCheckoutQuery

query predicate edges(Step a, Step b) { a.getNextStep() = b }

from PRHeadCheckoutStep checkout, PoisonableStep step, Event event
where criticalSeverityUntrustedCheckoutTOCTOU(checkout, step, event)
select checkout, checkout, step,
  "Insufficient protection against execution of untrusted code on a privileged workflow ($@).",
  event, event.getName()
