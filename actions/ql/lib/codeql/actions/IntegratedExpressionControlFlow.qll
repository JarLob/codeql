/** Provides an integrated view of Actions and expression-level control flow. */

import codeql.actions.Ast
import codeql.actions.Cfg as Cfg
import codeql.actions.ExpressionEvaluation
import codeql.actions.ExpressionControlFlow as ExpressionCfg
import codeql.actions.JobSynchronization as JobSync
import codeql.Locations
import codeql.controlflow.SuccessorType

private newtype TIntegratedNode =
  TActionsNode(Cfg::Node node) or
  TExpressionNode(ExpressionCfg::Node node)

/** A node in the integrated Actions and expression control-flow graph. */
abstract class Node extends TIntegratedNode {
  /** Gets an immediate successor. */
  Node getASuccessor() { result = this.getASuccessorWithType(_) }

  /** Gets an immediate successor with edge label `type`. */
  Node getASuccessorWithType(SuccessorType type) { integratedSuccessor(this, result, type) }

  /** Gets an immediate successor after evaluating known values for `event`. */
  Node getASuccessor(Event event) { result = this.getASuccessorForEvent(event, _) }

  /** Gets an event-feasible immediate successor with edge label `type`. */
  Node getASuccessorForEvent(Event event, SuccessorType type) {
    integratedSuccessorForEvent(this, result, event, type)
  }

  /** Gets an immediate predecessor. */
  Node getAPredecessor() { result.getASuccessor() = this }

  /** Gets an immediate predecessor after evaluating known values for `event`. */
  Node getAPredecessor(Event event) { result.getASuccessor(event) = this }

  /** Gets a reachable node, including this node. */
  Node getAReachableNode() { result = this or result = this.getASuccessor+() }

  /** Gets a reachable node for `event`, including this node. */
  Node getAReachableNode(Event event) { integratedScopeReachableForEvent(this, result, event) }

  /** Gets the shared Actions CFG scope containing this node. */
  Cfg::CfgScope getScope() {
    this instanceof ActionsNode and result = this.(ActionsNode).getCfgNode().getScope()
    or
    this instanceof ExpressionNode and
    result =
      getConditionNode(this.(ExpressionNode).getExpressionCfgNode().getExpression()).getScope()
  }

  /** Gets the containing source location. */
  Location getLocation() {
    this instanceof ActionsNode and result = this.(ActionsNode).getCfgNode().getLocation()
    or
    this instanceof ExpressionNode and
    result = this.(ExpressionNode).getExpressionCfgNode().getLocation()
  }

  abstract string toString();
}

/** An existing node in the shared Actions CFG. */
class ActionsNode extends Node, TActionsNode {
  Cfg::Node node;

  ActionsNode() { this = TActionsNode(node) }

  Cfg::Node getCfgNode() { result = node }

  override string toString() { result = node.toString() }
}

/** A node in the operand-level expression CFG. */
class ExpressionNode extends Node, TExpressionNode {
  ExpressionCfg::Node node;

  ExpressionNode() { this = TExpressionNode(node) }

  ExpressionCfg::Node getExpressionCfgNode() { result = node }

  override string toString() { result = node.toString() }
}

private If getAParsedCondition(Cfg::Node node) {
  result = node.getAstNode() and exists(result.getConditionExpr().getRoot())
}

private Cfg::Node getConditionNode(Expression expression) {
  exists(If condition |
    condition.getConditionExpr() = expression and result.getAstNode() = condition
  )
}

private predicate scopeHasEvent(Cfg::CfgScope scope, Event event) {
  exists(ActionsNode action, AstNode ast |
    action.getScope() = scope and
    ast = action.getCfgNode().getAstNode() and
    ast.getATriggerEvent() = event
  )
}

private predicate isRootCompletion(ExpressionCfg::Node node) {
  node instanceof ExpressionCfg::CompletionNode and
  node.getExpressionNode() instanceof ExpressionRoot
}

bindingset[predecessor, successor]
private predicate expressionEdgeType(
  ExpressionCfg::Node predecessor, ExpressionCfg::Node successor, SuccessorType type
) {
  predecessor instanceof ExpressionCfg::EvaluationNode and
  successor instanceof ExpressionCfg::CompletionNode and
  predecessor.getExpressionNode() = successor.getExpressionNode() and
  type.(BooleanSuccessor).getValue() = successor.(ExpressionCfg::CompletionNode).getOutcome()
  or
  not (
    predecessor instanceof ExpressionCfg::EvaluationNode and
    successor instanceof ExpressionCfg::CompletionNode and
    predecessor.getExpressionNode() = successor.getExpressionNode()
  ) and
  type instanceof DirectSuccessor
}

cached
private predicate integratedSuccessor(Node predecessor, Node successor, SuccessorType type) {
  exists(ActionsNode action, If condition |
    predecessor = action and
    condition = getAParsedCondition(action.getCfgNode()) and
    successor = TExpressionNode(ExpressionCfg::getEntryNode(condition.getConditionExpr())) and
    type instanceof DirectSuccessor
  )
  or
  exists(ActionsNode action |
    predecessor = action and
    not exists(getAParsedCondition(action.getCfgNode())) and
    successor = TActionsNode(action.getCfgNode().getASuccessor(type))
  )
  or
  exists(ExpressionNode expression |
    predecessor = expression and
    not isRootCompletion(expression.getExpressionCfgNode()) and
    successor = TExpressionNode(expression.getExpressionCfgNode().getASuccessor()) and
    expressionEdgeType(expression.getExpressionCfgNode(),
      successor.(ExpressionNode).getExpressionCfgNode(), type)
  )
  or
  exists(
    ExpressionNode expression, ExpressionCfg::CompletionNode completion, BooleanSuccessor branch,
    Cfg::Node conditionNode
  |
    predecessor = expression and
    completion = expression.getExpressionCfgNode() and
    completion.getExpressionNode() instanceof ExpressionRoot and
    conditionNode = getConditionNode(completion.getExpression()) and
    branch.getValue() = completion.getOutcome() and
    successor = TActionsNode(conditionNode.getASuccessor(branch)) and
    type instanceof DirectSuccessor
  )
}

cached
private predicate integratedSuccessorForEvent(
  Node predecessor, Node successor, Event event, SuccessorType type
) {
  predecessor.getScope() = successor.getScope() and
  scopeHasEvent(predecessor.getScope(), event) and
  (
    exists(ActionsNode action, If condition |
      predecessor = action and
      condition = getAParsedCondition(action.getCfgNode()) and
      successor = TExpressionNode(ExpressionCfg::getEntryNode(condition.getConditionExpr())) and
      type instanceof DirectSuccessor
    )
    or
    exists(ActionsNode action |
      predecessor = action and
      not exists(getAParsedCondition(action.getCfgNode())) and
      successor = TActionsNode(action.getCfgNode().getASuccessor(type))
    )
    or
    exists(ExpressionNode expression |
      predecessor = expression and
      not isRootCompletion(expression.getExpressionCfgNode()) and
      successor = TExpressionNode(expression.getExpressionCfgNode().getASuccessor(event)) and
      expressionEdgeType(expression.getExpressionCfgNode(),
        successor.(ExpressionNode).getExpressionCfgNode(), type)
    )
    or
    exists(
      ExpressionNode expression, ExpressionCfg::CompletionNode completion, BooleanSuccessor branch,
      Cfg::Node conditionNode
    |
      predecessor = expression and
      completion = expression.getExpressionCfgNode() and
      completion.getExpressionNode() instanceof ExpressionRoot and
      conditionNode = getConditionNode(completion.getExpression()) and
      branch.getValue() = completion.getOutcome() and
      successor = TActionsNode(conditionNode.getASuccessor(branch)) and
      type instanceof DirectSuccessor
    )
  )
}

private predicate integratedScopeReachableForEvent(Node source, Node target, Event event) {
  source.getScope() = target.getScope() and
  scopeHasEvent(source.getScope(), event) and
  (
    target = source
    or
    exists(ActionsNode action, ExpressionNode expression, If condition |
      source = action and
      target = expression and
      condition = getAParsedCondition(action.getCfgNode()) and
      expression.getExpressionCfgNode() =
        ExpressionCfg::getEntryNode(condition.getConditionExpr()).getAReachableNode(event)
    )
    or
    exists(ExpressionNode sourceExpression, ExpressionNode targetExpression |
      source = sourceExpression and
      target = targetExpression and
      sourceExpression.getExpressionCfgNode().getExpression() =
        targetExpression.getExpressionCfgNode().getExpression() and
      targetExpression.getExpressionCfgNode() =
        sourceExpression.getExpressionCfgNode().getAReachableNode(event)
    )
    or
    not target instanceof ExpressionNode and target = source.getAReachableNode()
  )
}

bindingset[source, target, event]
private predicate actionsMayReachForEvent(
  ActionsNode source, ActionsNode target, Event event
) {
  source.getScope() = target.getScope() and
  scopeHasEvent(source.getScope(), event) and
  (
    source = target
    or
    target.getCfgNode() = source.getCfgNode().getASuccessor+()
  )
}

private predicate hasModeledCommonScope(AstNode source, AstNode target) {
  exists(ActionsNode sourceNode, ActionsNode targetNode |
    sourceNode.getCfgNode().getAstNode() = source and
    targetNode.getCfgNode().getAstNode() = target and
    sourceNode.getScope() = targetNode.getScope()
  )
}

private predicate enclosingJobMayExecuteForEvent(AstNode node, Event event) {
  not exists(node.getEnclosingJob())
  or
  exists(Job job |
    job = node.getEnclosingJob() and
    job.getATriggerEvent() = event and
    (
      not exists(job.getANeededJob()) and
      (
        not exists(job.getIf())
        or
        exists(If condition |
          condition = job.getIf() and
          (
            exists(condition.getConditionExpr().getRoot()) and
            isConditionFeasible(condition, event)
            or
            not exists(condition.getConditionExpr().getRoot())
          )
        )
      )
      or
      exists(job.getANeededJob()) and JobSync::jobMayExecuteForEvent(job, event)
    )
  )
}

private predicate ownStepConditionMayPermitExecution(Step step, Event event) {
  not exists(step.getIf())
  or
  exists(If condition |
    condition = step.getIf() and
    (
      exists(condition.getConditionExpr().getRoot()) and isConditionFeasible(condition, event)
      or
      not exists(condition.getConditionExpr().getRoot())
    )
  )
}

private predicate stepAndCallerMayExecuteForEvent(Step step, Event event) {
  step.getATriggerEvent() = event and
  ownStepConditionMayPermitExecution(step, event) and
  (
    not exists(step.getEnclosingCompositeAction())
    or
    stepAndCallerMayExecuteForEvent(step.getEnclosingCompositeAction().getACallerStep(), event)
  )
}

private predicate stepMayExecuteForEvent(Step step, Event event) {
  enclosingJobMayExecuteForEvent(step, event) and stepAndCallerMayExecuteForEvent(step, event)
}

private predicate stepPrecedes(Step source, Step target) {
  target = source.getNextStep+() or target = source.getAFollowingStep()
}

/** Holds if `target` is ordered after `source` and both may execute for `event`. */
bindingset[source, target, event]
predicate orderedStepsMayReachForEvent(Step source, Step target, Event event) {
  source != target and
  source.getEnclosingJob() = target.getEnclosingJob() and
  stepPrecedes(source, target) and
  source.getATriggerEvent() = event and
  stepMayExecuteForEvent(source, event) and
  stepMayExecuteForEvent(target, event)
}

/** Holds if `target` is ordered after `source` and both may execute for a shared event. */
bindingset[source, target]
predicate orderedStepsMayReachForAnyEvent(Step source, Step target) {
  (
    exists(Event event |
      source.getATriggerEvent() = event and
      orderedStepsMayReachForEvent(source, target, event)
    )
    or
    not exists(source.getATriggerEvent())
  )
}

/** Holds if `node` may execute for `event` in its Actions CFG scope. */
bindingset[node, event]
predicate mayExecuteForEvent(AstNode node, Event event) {
  exists(Step step | step = node.getEnclosingStep() | stepMayExecuteForEvent(step, event))
  or
  not exists(node.getEnclosingStep()) and
  node.getATriggerEvent() = event and
  enclosingJobMayExecuteForEvent(node, event) and
  (
    not exists(ActionsNode nodeCfg | nodeCfg.getCfgNode().getAstNode() = node)
    or
    exists(ActionsNode entry, ActionsNode nodeCfg |
      entry.getCfgNode() instanceof Cfg::EntryNode and
      entry.getScope() = nodeCfg.getScope() and
      nodeCfg.getCfgNode().getAstNode() = node and
      actionsMayReachForEvent(entry, nodeCfg, event)
    )
  )
}

/**
 * Holds if `target` may execute after `source` for `event` in the same Actions CFG scope.
 * Reachability of `source` from the scope entry is also required, so its own guards are honored.
 */
bindingset[source, target, event]
predicate mayReachForEvent(AstNode source, AstNode target, Event event) {
  source != target and
  (
    exists(Step sourceStep, Step targetStep |
      source = sourceStep and
      target = targetStep and
      sourceStep.getEnclosingJob() = targetStep.getEnclosingJob() and
      stepPrecedes(sourceStep, targetStep) and
      stepMayExecuteForEvent(sourceStep, event) and
      stepMayExecuteForEvent(targetStep, event)
    )
    or
    not (
      source instanceof Step and
      target instanceof Step and
      source.getEnclosingJob() = target.getEnclosingJob()
    ) and
    source.getATriggerEvent() = event and
    enclosingJobMayExecuteForEvent(source, event) and
    enclosingJobMayExecuteForEvent(target, event) and
    (
      not hasModeledCommonScope(source, target)
      or
      source.getEnclosingWorkflow() = target.getEnclosingWorkflow() and
      exists(ActionsNode entry, ActionsNode sourceNode, ActionsNode targetNode |
        entry.getCfgNode() instanceof Cfg::EntryNode and
        entry.getScope() = sourceNode.getScope() and
        sourceNode.getScope() = targetNode.getScope() and
        sourceNode.getCfgNode().getAstNode() = source and
        targetNode.getCfgNode().getAstNode() = target and
        actionsMayReachForEvent(entry, sourceNode, event) and
        actionsMayReachForEvent(sourceNode, targetNode, event)
      )
    )
  )
}

/** Holds if `left` and `right` may both execute in one run for `event`. */
predicate mayCoExecuteForEvent(AstNode left, AstNode right, Event event) {
  left = right and mayExecuteForEvent(left, event)
  or
  mayReachForEvent(left, right, event)
  or
  mayReachForEvent(right, left, event)
}

/** Holds if `node` may execute for at least one statically known trigger event. */
predicate mayExecuteForAnyEvent(AstNode node) {
  exists(Event event | node.getATriggerEvent() = event | mayExecuteForEvent(node, event))
  or
  not exists(node.getATriggerEvent())
}

/** Holds if `target` may execute after `source` for at least one shared trigger event. */
predicate mayReachForAnyEvent(AstNode source, AstNode target) {
  exists(Event event | source.getATriggerEvent() = event | mayReachForEvent(source, target, event))
  or
  not exists(source.getATriggerEvent())
}

/** Holds if both nodes may execute for at least one shared trigger event. */
predicate mayCoExecuteForAnyEvent(AstNode left, AstNode right) {
  exists(Event event | left.getATriggerEvent() = event | mayCoExecuteForEvent(left, right, event))
  or
  not exists(left.getATriggerEvent())
}
