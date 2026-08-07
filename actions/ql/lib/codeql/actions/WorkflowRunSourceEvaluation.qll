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

/** Holds if both nodes may execute for this concrete workflow-run source event. */
bindingset[left, right, event, sourceEvent]
pragma[inline_late]
predicate workflowRunSourceMayCoExecute(AstNode left, AstNode right, Event event, Event sourceEvent) {
  mayExecuteForSource(left, event, sourceEvent) and
  mayExecuteForSource(right, event, sourceEvent) and
  IntegratedCfg::mayCoExecuteForEvent(left, right, event)
}

private newtype TWorkflowExecutionContext =
  TEventWorkflowExecutionContext(Event event) or
  TResolvedWorkflowRunExecutionContext(Event event, Event sourceEvent) or
  TUnresolvedWorkflowRunExecutionContext(Event event)

/** Gets an immediate predecessor whose run can initiate `event`. */
private Event getAProvenancePredecessor(Event event) {
  result = Dispatch::getADispatchCallerEvent(event)
  or
  event.getName() = "workflow_run" and
  event.acceptsExternalInputWorkflowRunSourceEvent(result)
}

/** Holds if `event` has a statically resolved directly external origin. */
private predicate hasDirectlyExternalOrigin(Event event) {
  event.isDirectlyExternallyTriggerable()
  or
  getAProvenancePredecessor+(event).isDirectlyExternallyTriggerable()
}

/**
 * A concrete workflow execution context.
 *
 * A context identifies the trigger event and, for a resolved `workflow_run`, the source event
 * whose run caused it.
 */
class WorkflowExecutionContext extends TWorkflowExecutionContext {
  WorkflowExecutionContext() {
    exists(Event event |
      this = TEventWorkflowExecutionContext(event) and event.getName() != "workflow_run"
    )
    or
    exists(Event event, Event sourceEvent |
      this = TResolvedWorkflowRunExecutionContext(event, sourceEvent) and
      event.getName() = "workflow_run" and
      event.acceptsWorkflowRunSourceEvent(sourceEvent)
    )
    or
    exists(Event event |
      this = TUnresolvedWorkflowRunExecutionContext(event) and
      event.getName() = "workflow_run" and
      event.hasFeasibleWorkflowRunActivityType() and
      event.hasUnresolvedWorkflowRunSource()
    )
  }

  string toString() {
    exists(Event event |
      this = TEventWorkflowExecutionContext(event) and
      result = "workflow execution context for " + event.toString()
    )
    or
    exists(Event event, Event sourceEvent |
      this = TResolvedWorkflowRunExecutionContext(event, sourceEvent) and
      result =
        "workflow execution context for " + event.toString() + " from " + sourceEvent.toString()
    )
    or
    exists(Event event |
      this = TUnresolvedWorkflowRunExecutionContext(event) and
      result = "workflow execution context for " + event.toString() + " from an unresolved source"
    )
  }

  /** Gets the event that triggers this execution context. */
  Event getEvent() {
    this = TEventWorkflowExecutionContext(result)
    or
    exists(Event sourceEvent | this = TResolvedWorkflowRunExecutionContext(result, sourceEvent))
    or
    this = TUnresolvedWorkflowRunExecutionContext(result)
  }

  /** Gets the resolved source event for a `workflow_run` context, if one is available. */
  Event getSourceEvent() { this = TResolvedWorkflowRunExecutionContext(_, result) }

  /** Holds if this execution is directly triggered by `pull_request`. */
  predicate isPullRequest() { this.getEvent().getName() = "pull_request" }

  /** Holds if input associated with `sourceEvent` is available in this context. */
  predicate acceptsSourceEvent(Event sourceEvent) {
    exists(Event event |
      this = TEventWorkflowExecutionContext(event) and
      (
        sourceEvent = event
        or
        sourceEvent = Dispatch::getADispatchCallerEvent+(event)
      )
    )
    or
    exists(Event event, Event workflowRunSource |
      this = TResolvedWorkflowRunExecutionContext(event, workflowRunSource) and
      (
        sourceEvent = [event, workflowRunSource]
        or
        sourceEvent = Dispatch::getADispatchCallerEvent+(workflowRunSource)
      )
    )
    or
    this = TUnresolvedWorkflowRunExecutionContext(sourceEvent)
  }

  /** Holds if `node` may execute in this context. */
  predicate mayExecute(AstNode node) {
    exists(Event event |
      this = TEventWorkflowExecutionContext(event) and
      IntegratedCfg::mayExecuteForEvent(node, event)
    )
    or
    exists(Event event, Event sourceEvent |
      this = TResolvedWorkflowRunExecutionContext(event, sourceEvent) and
      mayExecuteForSource(node, event, sourceEvent)
    )
    or
    exists(Event event |
      this = TUnresolvedWorkflowRunExecutionContext(event) and
      IntegratedCfg::mayExecuteForEvent(node, event)
    )
  }

  /** Holds if both nodes may execute in this context. */
  predicate mayCoExecute(AstNode left, AstNode right) {
    exists(Event event |
      this = TEventWorkflowExecutionContext(event) and
      IntegratedCfg::mayCoExecuteForEvent(left, right, event)
    )
    or
    exists(Event event, Event sourceEvent |
      this = TResolvedWorkflowRunExecutionContext(event, sourceEvent) and
      workflowRunSourceMayCoExecute(left, right, event, sourceEvent)
    )
    or
    exists(Event event |
      this = TUnresolvedWorkflowRunExecutionContext(event) and
      IntegratedCfg::mayCoExecuteForEvent(left, right, event)
    )
  }

  /** Holds if `node` executes with privileged credentials in this context. */
  predicate isPrivileged(AstNode node) {
    exists(Event event |
      this = TEventWorkflowExecutionContext(event) and
      node.getEnclosingJob().isPrivilegedForEvent(event) and
      this.mayExecute(node)
    )
    or
    exists(Event event, Event sourceEvent |
      this = TResolvedWorkflowRunExecutionContext(event, sourceEvent) and
      node.getEnclosingJob().isPrivilegedForEvent(event) and
      mayExecuteForSource(node, event, sourceEvent)
    )
    or
    exists(Event event |
      this = TUnresolvedWorkflowRunExecutionContext(event) and
      node.getEnclosingJob().isPrivilegedForEvent(event) and
      IntegratedCfg::mayExecuteForEvent(node, event)
    )
  }

  /** Holds if this execution was initiated by a directly external event or dispatch caller. */
  predicate isDirectlyExternallyInitiated() {
    exists(Event event |
      this = TEventWorkflowExecutionContext(event) and hasDirectlyExternalOrigin(event)
    )
    or
    exists(Event event, Event sourceEvent |
      this = TResolvedWorkflowRunExecutionContext(event, sourceEvent) and
      event.acceptsExternalInputWorkflowRunSourceEvent(sourceEvent) and
      hasDirectlyExternalOrigin(sourceEvent)
    )
    or
    // Keep unresolved workflow-run provenance conservative.
    this = TUnresolvedWorkflowRunExecutionContext(_)
  }
}

/** Gets a workflow execution context for `event`. */
bindingset[event]
pragma[inline_late]
WorkflowExecutionContext getAWorkflowExecutionContext(Event event) { result.getEvent() = event }

/** Gets a workflow execution context in which `node` may execute. */
bindingset[node]
pragma[inline_late]
WorkflowExecutionContext getAWorkflowExecutionContextForNode(AstNode node) {
  result.mayExecute(node)
}

/** Gets a workflow execution context in which both nodes may execute. */
bindingset[left, right]
pragma[inline_late]
WorkflowExecutionContext getAWorkflowExecutionContextForNodes(AstNode left, AstNode right) {
  result.mayCoExecute(left, right)
}

/** Gets a workflow execution context in which `node` has privileged credentials. */
bindingset[node]
pragma[inline_late]
WorkflowExecutionContext getAPrivilegedWorkflowExecutionContext(AstNode node) {
  result.isPrivileged(node)
}
