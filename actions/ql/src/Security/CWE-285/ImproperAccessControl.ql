/**
 * @name Improper Access Control
 * @description The access control mechanism is not properly implemented, allowing untrusted code to be executed in a privileged context.
 * @kind problem
 * @problem.severity error
 * @precision high
 * @security-severity 9.3
 * @id actions/improper-access-control
 * @tags actions
 *       security
 *       external/cwe/cwe-285
 */

import codeql.actions.security.UntrustedCheckoutQuery
import codeql.actions.security.ControlChecks

from AuthorizationAttemptCheck check, PRHeadCheckoutStep checkout, Event event
where
  knownImproperCheckoutAuthorization(checkout, event, check) and
  // Preserve the query's existing high-severity privileged-context threshold.
  workflowRunAwarePrivilegedContext(checkout, event)
select checkout,
  "The authorization check $@ does not prevent untrusted code from running in a privileged context.",
  check, check.toString()
