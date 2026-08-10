import codeql.actions.Ast
import codeql.actions.ExpressionEvaluation
import codeql.Locations

private ExpressionNode getAControlChild(ExpressionNode parent) {
  parent instanceof ExpressionRoot and result = parent.getChild(0)
  or
  parent instanceof BinaryExpression and
  parent.(BinaryExpression).getOperator() = ["&&", "||"] and
  result = [parent.(BinaryExpression).getLeftOperand(), parent.(BinaryExpression).getRightOperand()]
  or
  parent instanceof UnaryExpression and result = parent.(UnaryExpression).getOperand()
}

private predicate isControlFlowExpressionNode(ExpressionNode node) {
  exists(ExpressionRoot root | node = root or node = getAControlChild*(root))
}

private predicate isAtomicCondition(ExpressionNode node) {
  isControlFlowExpressionNode(node) and
  not node instanceof ExpressionRoot and
  not node instanceof UnaryExpression and
  not exists(BinaryExpression binary | node = binary and binary.getOperator() = ["&&", "||"])
}

private newtype TNode =
  TEvaluationNode(ExpressionNode expression) { isControlFlowExpressionNode(expression) } or
  TCompletionNode(ExpressionNode expression, boolean outcome) {
    isControlFlowExpressionNode(expression) and outcome in [false, true]
  }

/** A node in the control-flow graph of a parsed GitHub Actions expression. */
abstract class Node extends TNode {
  /** Gets the parsed expression represented by this node. */
  abstract ExpressionNode getExpressionNode();

  /** Gets the root expression containing this node. */
  ExpressionRoot getRoot() { result = this.getExpressionNode().getParent*() }

  /** Gets the enclosing workflow expression. */
  Expression getExpression() { result = this.getExpressionNode().getExpression() }

  /** Gets the location of the containing workflow expression. */
  Location getLocation() { result = this.getExpression().getLocation() }

  /** Holds if this node has the specified parsed-expression source span. */
  predicate hasSourceLocation(string path, int sl, int sc, int el, int ec) {
    this.getExpressionNode().hasSourceLocation(path, sl, sc, el, ec)
  }

  /** Holds if the parsed-expression source span is exact. */
  predicate hasExactSourceLocation() { this.getExpressionNode().hasExactSourceLocation() }

  /** Gets a context-independent successor. */
  Node getASuccessor() { expressionSuccessor(this, result) }

  /** Gets a successor after evaluating statically known values for `event`. */
  Node getASuccessor(Event event) { expressionSuccessorForEvent(this, result, event) }

  /** Gets a context-independent predecessor. */
  Node getAPredecessor() { result.getASuccessor() = this }

  /** Gets a predecessor after evaluating statically known values for `event`. */
  Node getAPredecessor(Event event) { result.getASuccessor(event) = this }

  /** Gets a context-independent reachable node, including this node. */
  Node getAReachableNode() { result = this or result = this.getASuccessor+() }

  /** Gets a reachable node for `event`, including this node. */
  bindingset[this, event]
  pragma[inline_late]
  Node getAReachableNode(Event event) {
    result = this
    or
    exists(EventNode source, EventNode target |
      source = TExpressionEventNode(this, event) and
      target = source.getASuccessor+() and
      result = target.getNode()
    )
  }

  abstract string toString();
}

/** A state in which an expression is about to be evaluated. */
class EvaluationNode extends Node, TEvaluationNode {
  ExpressionNode expression;

  EvaluationNode() { this = TEvaluationNode(expression) }

  override ExpressionNode getExpressionNode() { result = expression }

  override string toString() { result = "evaluate " + expression.toString() }
}

/** A state in which an expression has completed with a Boolean outcome. */
class CompletionNode extends Node, TCompletionNode {
  ExpressionNode expression;
  boolean outcome;

  CompletionNode() { this = TCompletionNode(expression, outcome) }

  override ExpressionNode getExpressionNode() { result = expression }

  /** Gets the Boolean outcome of the completed expression. */
  boolean getOutcome() { result = outcome }

  override string toString() {
    result = "complete " + expression.toString() + " as " + outcome.toString()
  }
}

private newtype TEventNode =
  TExpressionEventNode(Node node, Event event) {
    node.getExpression().getATriggerEvent() = event
  }

private class EventNode extends TEventNode, TExpressionEventNode {
  Node node;
  Event event;

  EventNode() { this = TExpressionEventNode(node, event) }

  Node getNode() { result = node }

  EventNode getASuccessor() {
    result = TExpressionEventNode(node.getASuccessor(event), event)
  }

  string toString() { result = node + " / " + event }
}

bindingset[expression, outcome]
pragma[inline_late]
private TNode getCompletionNode(ExpressionNode expression, boolean outcome) {
  result = TCompletionNode(expression, outcome)
}

cached
private predicate structuralSuccessor(Node predecessor, Node successor) {
  predecessor instanceof EvaluationNode and
  predecessor.getExpressionNode() instanceof ExpressionRoot and
  successor = TEvaluationNode(getAControlChild(predecessor.getExpressionNode()))
  or
  predecessor instanceof EvaluationNode and
  predecessor.getExpressionNode() instanceof UnaryExpression and
  successor = TEvaluationNode(predecessor.getExpressionNode().(UnaryExpression).getOperand())
  or
  predecessor instanceof EvaluationNode and
  predecessor.getExpressionNode() instanceof BinaryExpression and
  predecessor.getExpressionNode().(BinaryExpression).getOperator() = ["&&", "||"] and
  successor = TEvaluationNode(predecessor.getExpressionNode().(BinaryExpression).getLeftOperand())
  or
  exists(CompletionNode completion, ExpressionRoot root |
    predecessor = completion and
    root = completion.getExpressionNode().getParent() and
    successor = getCompletionNode(root, completion.getOutcome())
  )
  or
  exists(CompletionNode completion, UnaryExpression unary |
    predecessor = completion and
    unary = completion.getExpressionNode().getParent() and
    successor = getCompletionNode(unary, completion.getOutcome().booleanNot())
  )
  or
  exists(CompletionNode completion, BinaryExpression binary |
    predecessor = completion and
    binary = completion.getExpressionNode().getParent() and
    binary.getOperator() = "&&" and
    (
      completion.getExpressionNode() = binary.getLeftOperand() and
      completion.getOutcome() = true and
      successor = TEvaluationNode(binary.getRightOperand())
      or
      completion.getExpressionNode() = binary.getLeftOperand() and
      completion.getOutcome() = false and
      successor = getCompletionNode(binary, false)
      or
      completion.getExpressionNode() = binary.getRightOperand() and
      successor = getCompletionNode(binary, completion.getOutcome())
    )
  )
  or
  exists(CompletionNode completion, BinaryExpression binary |
    predecessor = completion and
    binary = completion.getExpressionNode().getParent() and
    binary.getOperator() = "||" and
    (
      completion.getExpressionNode() = binary.getLeftOperand() and
      completion.getOutcome() = false and
      successor = TEvaluationNode(binary.getRightOperand())
      or
      completion.getExpressionNode() = binary.getLeftOperand() and
      completion.getOutcome() = true and
      successor = getCompletionNode(binary, true)
      or
      completion.getExpressionNode() = binary.getRightOperand() and
      successor = getCompletionNode(binary, completion.getOutcome())
    )
  )
}

cached
private predicate expressionSuccessor(Node predecessor, Node successor) {
  structuralSuccessor(predecessor, successor)
  or
  exists(EvaluationNode evaluation, boolean outcome |
    predecessor = evaluation and
    isAtomicCondition(evaluation.getExpressionNode()) and
    outcome in [false, true] and
    successor = getCompletionNode(evaluation.getExpressionNode(), outcome)
  )
}

cached
private predicate expressionSuccessorForEvent(Node predecessor, Node successor, Event event) {
  predecessor.getExpression() = successor.getExpression() and
  predecessor.getExpression().getATriggerEvent() = event and
  (
    structuralSuccessor(predecessor, successor)
    or
    exists(EvaluationNode evaluation, boolean outcome |
      predecessor = evaluation and
      isAtomicCondition(evaluation.getExpressionNode()) and
      exists(If condition |
        condition.getConditionExpr() = evaluation.getExpressionNode().getExpression() and
        mayEvaluateConditionToBoolean(condition, evaluation.getExpressionNode(), event, outcome)
      ) and
      successor = getCompletionNode(evaluation.getExpressionNode(), outcome)
    )
  )
}

/** Gets the entry node for a parsed expression. */
EvaluationNode getEntryNode(Expression expression) {
  result = TEvaluationNode(expression.getRoot())
}

/** Gets a final completion of a parsed expression. */
CompletionNode getACompletionNode(Expression expression) {
  result = TCompletionNode(expression.getRoot(), _)
}
