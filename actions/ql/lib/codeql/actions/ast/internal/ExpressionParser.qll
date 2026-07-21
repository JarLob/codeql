private import Ast
private import ExpressionParserCore

class ExpressionNodeImpl extends ItemNode {
  ExpressionNodeImpl() { this.isInSyntaxTree() and this.isVisible() }

  ExpressionNodeImpl getAChild() { result = this.getVisibleChild(_) }

  ExpressionNodeImpl getChild(int i) { result = this.getVisibleChild(i) }

  ExpressionNodeImpl getParent() { result.getAChild() = this }

  string getKind() {
    if this.isTopNode() then result = "root" else result = this.getProduction().getLhs()
  }

  int getStartOffset() { result = this.getStart() }

  int getEndOffset() { result = this.getEnd() }

  int getRunnerDepth() {
    result =
      max(int depth |
        exists(ExpressionNodeImpl descendant | runnerDescendantDepth(this, descendant, depth))
      |
        depth
      )
  }

  override string toString() { result = this.getKind() + "(" + this.getText() + ")" }
}

private ExpressionNodeImpl getALogicalOperand(BinaryExpressionImpl binary) {
  exists(ExpressionNodeImpl direct | direct = [binary.getLeftOperand(), binary.getRightOperand()] |
    if
      binary.getOperator() = ["&&", "||"] and
      direct instanceof BinaryExpressionImpl and
      direct.(BinaryExpressionImpl).getOperator() = binary.getOperator()
    then result = getALogicalOperand(direct.(BinaryExpressionImpl))
    else result = direct
  )
}

private ExpressionNodeImpl getARunnerChild(ExpressionNodeImpl parent) {
  parent instanceof BinaryExpressionImpl and
  parent.(BinaryExpressionImpl).getOperator() = ["&&", "||"] and
  result = getALogicalOperand(parent.(BinaryExpressionImpl))
  or
  parent instanceof BinaryExpressionImpl and
  parent.(BinaryExpressionImpl).getOperator() != ["&&", "||"] and
  result =
    [
      parent.(BinaryExpressionImpl).getLeftOperand(),
      parent.(BinaryExpressionImpl).getRightOperand()
    ]
  or
  parent instanceof UnaryExpressionImpl and
  result = parent.(UnaryExpressionImpl).getOperand()
  or
  parent instanceof FunctionCallExpressionImpl and
  result = parent.(FunctionCallExpressionImpl).getArgument(_)
  or
  parent instanceof AccessExpressionImpl and
  (
    result = parent.(AccessExpressionImpl).getBase()
    or
    parent.(AccessExpressionImpl).getAccessor() instanceof IndexAccessExpressionImpl and
    result = parent.(AccessExpressionImpl).getAccessor().(IndexAccessExpressionImpl).getIndex()
    or
    not parent.(AccessExpressionImpl).getAccessor() instanceof IndexAccessExpressionImpl and
    result = parent.(AccessExpressionImpl).getAccessor()
  )
}

private predicate runnerDescendantDepth(ExpressionNodeImpl root, ExpressionNodeImpl node, int depth) {
  node = root and depth = 1
  or
  exists(ExpressionNodeImpl parent, int parentDepth |
    node = getARunnerChild(parent) and
    runnerDescendantDepth(root, parent, parentDepth) and
    depth = parentDepth + 1
  )
}

private predicate hasValidWellKnownFunctionArity(FunctionCallExpressionImpl call) {
  exists(string name, int argumentCount |
    name = call.getCallee().getName().toLowerCase() and
    argumentCount = count(call.getArgument(_))
  |
    name = "case" and argumentCount in [3 .. 255] and argumentCount % 2 = 1
    or
    name = ["contains", "endswith", "startswith"] and argumentCount = 2
    or
    name = ["fromjson", "tojson"] and argumentCount = 1
    or
    name = "join" and argumentCount in [1, 2]
    or
    name = "format" and argumentCount in [1 .. 255]
    or
    not name =
      ["case", "contains", "endswith", "startswith", "fromjson", "tojson", "join", "format"]
  )
}

class ExpressionRootImpl extends ExpressionNodeImpl {
  ExpressionRootImpl() {
    this.isTopNode() and
    this.getChild(0).getRunnerDepth() <= 50 and
    forall(FunctionCallExpressionImpl call | call.getExpression() = this.getExpression() |
      hasValidWellKnownFunctionArity(call)
    )
  }
}

class BinaryExpressionImpl extends ExpressionNodeImpl {
  BinaryExpressionImpl() {
    this.getKind() = ["OrExpression", "AndExpression", "EqualityExpression", "ComparisonExpression"]
  }

  ExpressionNodeImpl getLeftOperand() { result = this.getChild(0) }

  ExpressionNodeImpl getRightOperand() { result = this.getChild(1) }

  string getOperator() {
    exists(ItemNode operator |
      operator = this.getARawChild() and
      operator.getProduction().getLhs() =
        ["_OrOperator", "_AndOperator", "_EqualityOperator", "_ComparisonOperator"] and
      result = operator.getText().trim()
    )
  }
}

class UnaryExpressionImpl extends ExpressionNodeImpl {
  UnaryExpressionImpl() { this.getKind() = "NotExpression" }

  ExpressionNodeImpl getOperand() { result = this.getChild(0) }

  string getOperator() { result = "!" }
}

class IdentifierExpressionImpl extends ExpressionNodeImpl {
  IdentifierExpressionImpl() {
    this.getProduction().getLhs() = ["Identifier", "PropertyIdentifier"]
  }

  override string getKind() { result = "Identifier" }

  string getName() { result = this.getText() }
}

class FunctionCallExpressionImpl extends ExpressionNodeImpl {
  FunctionCallExpressionImpl() { this.getKind() = "FunctionCall" }

  IdentifierExpressionImpl getCallee() { result = this.getChild(0) }

  ExpressionNodeImpl getArgument(int i) { i >= 0 and result = this.getChild(i + 1) }
}

class AccessExpressionImpl extends ExpressionNodeImpl {
  AccessExpressionImpl() { this.getKind() = "AccessExpression" }

  ExpressionNodeImpl getBase() { result = this.getChild(0) }

  ExpressionNodeImpl getAccessor() { result = this.getChild(1) }
}

class PropertyAccessExpressionImpl extends ExpressionNodeImpl {
  PropertyAccessExpressionImpl() { this.getKind() = "PropertyAccess" }

  string getName() { result = this.getChild(0).getText() }
}

class WildcardAccessExpressionImpl extends ExpressionNodeImpl {
  WildcardAccessExpressionImpl() { this.getKind() = "WildcardAccess" }
}

class IndexAccessExpressionImpl extends ExpressionNodeImpl {
  IndexAccessExpressionImpl() { this.getKind() = "IndexAccess" }

  ExpressionNodeImpl getIndex() { result = this.getChild(0) }
}

class LiteralExpressionImpl extends ExpressionNodeImpl {
  LiteralExpressionImpl() {
    this.getKind() = ["BooleanLiteral", "NullLiteral", "NumberLiteral", "StringLiteral"]
  }

  string getValue() { result = this.getText() }
}
