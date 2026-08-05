import codeql.actions.Ast
private import codeql.actions.ExpressionEvaluation as Evaluation
private import codeql.actions.IntegratedExpressionControlFlow as IntegratedCfg

private predicate conditionMayPermitSource(If condition, Event event, Event sourceEvent) {
  not exists(condition.getConditionExpr().getRoot())
  or
  Evaluation::isConditionFeasible(condition, event, sourceEvent)
}

private predicate jobConditionMayPermitSource(Job job, Event event, Event sourceEvent) {
  not exists(job.getIf())
  or
  conditionMayPermitSource(job.getIf(), event, sourceEvent)
}

private predicate stepConditionMayPermitSource(Step step, Event event, Event sourceEvent) {
  not exists(step.getIf())
  or
  conditionMayPermitSource(step.getIf(), event, sourceEvent)
}

private predicate stepConditionsMayPermitSource(Step step, Event event, Event sourceEvent) {
  stepConditionMayPermitSource(step, event, sourceEvent) and
  (
    not exists(step.getEnclosingCompositeAction())
    or
    stepConditionsMayPermitSource(step.getEnclosingCompositeAction().getACallerStep(), event,
      sourceEvent)
  )
}

/** Holds if `node` may execute for this locally resolved workflow-run source event. */
predicate mayExecuteForSource(AstNode node, Event event, Event sourceEvent) {
  event.acceptsWorkflowRunSourceEvent(sourceEvent) and
  IntegratedCfg::mayExecuteForEvent(node, event) and
  jobConditionMayPermitSource(node.getEnclosingJob(), event, sourceEvent) and
  (
    not exists(node.getEnclosingStep())
    or
    stepConditionsMayPermitSource(node.getEnclosingStep(), event, sourceEvent)
  )
}

/** Holds if `node` may execute in an externally triggered workflow-run source context. */
predicate mayExecuteForExternalSource(AstNode node, Event event) {
  event.getName() = "workflow_run" and
  event.hasFeasibleWorkflowRunActivityType() and
  (
    exists(Event sourceEvent |
      event.acceptsExternalWorkflowRunSourceEvent(sourceEvent) and
      mayExecuteForSource(node, event, sourceEvent)
    )
    or
    event.hasUnresolvedWorkflowRunSource() and
    IntegratedCfg::mayExecuteForEvent(node, event)
  )
}

/** Holds if both nodes may execute for this concrete workflow-run source event. */
bindingset[left, right, event, sourceEvent]
pragma[inline_late]
predicate workflowRunSourceMayCoExecute(AstNode left, AstNode right, Event event, Event sourceEvent) {
  mayExecuteForSource(left, event, sourceEvent) and
  mayExecuteForSource(right, event, sourceEvent) and
  IntegratedCfg::mayCoExecuteForEvent(left, right, event)
}

/** Holds if `node` may execute in a trigger context reachable by an external actor. */
predicate workflowRunAwareExternallyTriggerableContext(AstNode node, Event event) {
  event.getName() != "workflow_run" and
  event.isExternallyTriggerable() and
  IntegratedCfg::mayExecuteForEvent(node, event)
  or
  event.getName() = "workflow_run" and mayExecuteForExternalSource(node, event)
}

/** Holds if both nodes may execute for the same externally triggered source context. */
bindingset[left, right, event]
pragma[inline_late]
predicate workflowRunAwareMayCoExecute(AstNode left, AstNode right, Event event) {
  event.getName() != "workflow_run" and
  event.isExternallyTriggerable() and
  IntegratedCfg::mayCoExecuteForEvent(left, right, event)
  or
  event.getName() = "workflow_run" and
  event.hasFeasibleWorkflowRunActivityType() and
  (
    exists(Event sourceEvent |
      event.acceptsExternalWorkflowRunSourceEvent(sourceEvent) and
      mayExecuteForSource(left, event, sourceEvent) and
      mayExecuteForSource(right, event, sourceEvent) and
      IntegratedCfg::mayCoExecuteForEvent(left, right, event)
    )
    or
    event.hasUnresolvedWorkflowRunSource() and
    IntegratedCfg::mayCoExecuteForEvent(left, right, event)
  )
}

/** Holds if `node` executes in a privileged context reachable by an external actor. */
predicate workflowRunAwarePrivilegedContext(AstNode node, Event event) {
  event.getName() != "workflow_run" and
  node.getEnclosingJob().isPrivilegedExternallyTriggerable(event)
  or
  event.getName() = "workflow_run" and
  node.getEnclosingJob().isPrivilegedForEvent(event) and
  mayExecuteForExternalSource(node, event)
}

/** Holds if `node` has no externally reachable privileged trigger context. */
predicate workflowRunAwareNonPrivilegedContext(AstNode node) {
  not exists(Event event | workflowRunAwarePrivilegedContext(node, event))
}
