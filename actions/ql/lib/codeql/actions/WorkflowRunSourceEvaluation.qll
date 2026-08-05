import codeql.actions.Ast
import codeql.actions.ProgrammaticDispatch as Dispatch
private import codeql.actions.ExpressionEvaluation as Evaluation
private import codeql.actions.IntegratedExpressionControlFlow as IntegratedCfg

bindingset[condition, event, sourceEvent]
pragma[inline_late]
private predicate conditionMayPermitSource(If condition, Event event, Event sourceEvent) {
  not exists(condition.getConditionExpr().getRoot())
  or
  Evaluation::isConditionFeasible(condition, event, sourceEvent)
}

bindingset[job, event, sourceEvent]
pragma[inline_late]
private predicate jobConditionMayPermitSource(Job job, Event event, Event sourceEvent) {
  not exists(job.getIf())
  or
  conditionMayPermitSource(job.getIf(), event, sourceEvent)
}

bindingset[step, event, sourceEvent]
pragma[inline_late]
private predicate stepConditionMayPermitSource(Step step, Event event, Event sourceEvent) {
  not exists(step.getIf())
  or
  conditionMayPermitSource(step.getIf(), event, sourceEvent)
}

private Step getAStepOrEnclosingCallerStep(Step step) {
  result = step
  or
  exists(CompositeAction action |
    action = step.getEnclosingCompositeAction() and
    result = getAStepOrEnclosingCallerStep(action.getACallerStep())
  )
}

bindingset[step, event, sourceEvent]
pragma[inline_late]
private predicate stepConditionsMayPermitSource(Step step, Event event, Event sourceEvent) {
  forall(Step relevantStep | relevantStep = getAStepOrEnclosingCallerStep(step) |
    stepConditionMayPermitSource(relevantStep, event, sourceEvent)
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

/** Holds if `node` may execute for a workflow-run source that can expose external input. */
predicate mayExecuteForExternalInputSource(AstNode node, Event event) {
  event.getName() = "workflow_run" and
  event.hasFeasibleWorkflowRunActivityType() and
  (
    exists(Event sourceEvent |
      event.acceptsExternalInputWorkflowRunSourceEvent(sourceEvent) and
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

/** Holds if `node` may execute in a context relevant to externally controlled input. */
predicate workflowRunAwareExternalInputContext(AstNode node, Event event) {
  event.getName() != "workflow_run" and
  Dispatch::isExternalInputRelevant(event) and
  IntegratedCfg::mayExecuteForEvent(node, event)
  or
  event.getName() = "workflow_run" and mayExecuteForExternalInputSource(node, event)
}

/** Holds if both nodes may execute for the same external-input source context. */
bindingset[left, right, event]
pragma[inline_late]
predicate workflowRunAwareMayCoExecuteForExternalInput(AstNode left, AstNode right, Event event) {
  event.getName() != "workflow_run" and
  Dispatch::isExternalInputRelevant(event) and
  IntegratedCfg::mayCoExecuteForEvent(left, right, event)
  or
  event.getName() = "workflow_run" and
  event.hasFeasibleWorkflowRunActivityType() and
  (
    exists(Event sourceEvent |
      event.acceptsExternalInputWorkflowRunSourceEvent(sourceEvent) and
      mayExecuteForSource(left, event, sourceEvent) and
      mayExecuteForSource(right, event, sourceEvent) and
      IntegratedCfg::mayCoExecuteForEvent(left, right, event)
    )
    or
    event.hasUnresolvedWorkflowRunSource() and
    IntegratedCfg::mayCoExecuteForEvent(left, right, event)
  )
}

/** Holds if `node` executes in a privileged external-input context. */
predicate workflowRunAwarePrivilegedExternalInputContext(AstNode node, Event event) {
  event.getName() != "workflow_run" and
  Dispatch::isPrivilegedForExternalInput(node.getEnclosingJob(), event)
  or
  event.getName() = "workflow_run" and
  node.getEnclosingJob().isPrivilegedForEvent(event) and
  mayExecuteForExternalInputSource(node, event)
}

/** Holds if `node` has no privileged external-input context. */
predicate workflowRunAwareNonPrivilegedExternalInputContext(AstNode node) {
  not exists(Event event | workflowRunAwarePrivilegedExternalInputContext(node, event))
}
