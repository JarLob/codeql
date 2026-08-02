/**
 * @name Checkout of untrusted code in a privileged context
 * @description Privileged workflows have read/write access to the base repository and access to secrets.
 *              By explicitly checking out and running the build script from a fork the untrusted code is running in an environment
 *              that is able to push to the base repository and to access secrets.
 * @kind problem
 * @problem.severity error
 * @precision high
 * @security-severity 7.5
 * @id actions/untrusted-checkout/high
 * @tags actions
 *       security
 *       external/cwe/cwe-829
 */

import actions
import codeql.actions.security.UntrustedCheckoutQuery

from PRHeadCheckoutStep checkout, Event event
where highSeverityUntrustedCheckout(checkout, event)
select checkout,
  "Checkout of untrusted code in a privileged workflow with later potential execution (event trigger: $@).",
  event, event.getName()
