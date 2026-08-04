/**
 * @name Artifact Poisoning (Path Traversal)
 * @description An attacker may be able to poison the workflow's artifacts and influence on consequent steps.
 * @kind problem
 * @problem.severity error
 * @precision very-high
 * @security-severity 9
 * @id actions/artifact-poisoning/path-traversal
 * @tags actions
 *       security
 *       experimental
 *       external/cwe/cwe-829
 */

import actions
import codeql.actions.security.PoisonableSteps
import codeql.actions.security.UseOfKnownVulnerableActionQuery
import codeql.actions.IntegratedExpressionControlFlow as IntegratedCfg

from UsesStep download, KnownVulnerableAction vulnerable_action, Event event
where
  event = download.getATriggerEvent() and
  IntegratedCfg::mayExecuteForEvent(download, event) and
  vulnerable_action.getVulnerableAction() = download.getCallee() and
  download.getCallee() = "actions/download-artifact" and
  (
    download.getVersion() = vulnerable_action.getVulnerableVersion() or
    download.getVersion() = vulnerable_action.getVulnerableSha()
  ) and
  (
    // exists a poisonable upload artifact in the same workflow
    exists(UsesStep checkout, PoisonableStep poison, UsesStep upload |
      download.getEnclosingWorkflow().getAJob().(LocalJob).getAContainedStep() = checkout and
      workflowRunAwarePrivilegedContext(download, event) and
      checkout.getCallee() = "actions/checkout" and
      checkout.getAFollowingStep() = poison and
      IntegratedCfg::orderedStepsMayReachForEvent(checkout, poison, event) and
      poison.getAFollowingStep() = upload and
      IntegratedCfg::orderedStepsMayReachForEvent(poison, upload, event) and
      upload.getCallee() = "actions/upload-artifact"
    )
    or
    // upload artifact is not used in the same workflow
    not download.getEnclosingWorkflow().getAJob().(LocalJob).getAContainedStep() instanceof UsesStep
  )
select download, "Potential artifact poisoning"
