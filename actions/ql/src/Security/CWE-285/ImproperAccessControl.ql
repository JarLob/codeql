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
private import codeql.actions.security.ControlCheckConditions as Conditions

private predicate isStalePullRequestApprovalTrigger(Event event) {
  event.getName() = "pull_request_target" and
  event.getAnActivityType() = ["synchronize", "reopened"]
}

from LocalJob job, LabelIfCheck check, PRHeadCheckoutStep checkout, Event event
where
  job.isPrivilegedExternallyTriggerable(event) and
  job.getAContainedStep() = checkout and
  check.dominates(checkout, event) and
  not Conditions::conditionRequiresPullRequestRepositoryCheck(check) and
  (
    job.getATriggerEvent() = event and
    isStalePullRequestApprovalTrigger(event)
    or
    not exists(job.getATriggerEvent())
  )
select checkout,
  "The pull request code can change after the authorization check $@ and trigger another privileged run.",
  check, check.toString()
