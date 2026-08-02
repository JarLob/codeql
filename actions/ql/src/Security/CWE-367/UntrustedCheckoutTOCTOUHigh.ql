/**
 * @name Untrusted Checkout TOCTOU
 * @description Untrusted Checkout is protected by a security check but the checked-out branch can be changed after the check.
 * @kind problem
 * @problem.severity error
 * @precision high
 * @security-severity 7.5
 * @id actions/untrusted-checkout-toctou/high
 * @tags actions
 *       security
 *       external/cwe/cwe-367
 */

import actions
import codeql.actions.security.UntrustedCheckoutQuery

from PRHeadCheckoutStep checkout, Event event
where highSeverityUntrustedCheckoutTOCTOU(checkout, event)
select checkout,
  "Insufficient protection against execution of untrusted code on a privileged workflow ($@).",
  event, event.getName()
