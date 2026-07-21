/** Provides an integrated view of Actions and expression-level control flow. */

import codeql.actions.Ast
import codeql.actions.Cfg as Cfg
import codeql.actions.ExpressionControlFlow as ExpressionCfg
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
  Node getAReachableNode(Event event) { integratedReachableForEvent(this, result, event) }

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

private predicate isRootCompletion(ExpressionCfg::Node node) {
  node instanceof ExpressionCfg::CompletionNode and
  node.getExpressionNode() instanceof ExpressionRoot
}

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
}

cached
private predicate integratedReachableForEvent(Node source, Node target, Event event) {
  target = source
  or
  exists(Node predecessor |
    integratedReachableForEvent(source, predecessor, event) and
    integratedSuccessorForEvent(predecessor, target, event, _)
  )
}
