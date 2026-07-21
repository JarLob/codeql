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

  override string toString() { result = this.getKind() + "(" + this.getText() + ")" }
}

class ExpressionRootImpl extends ExpressionNodeImpl {
  ExpressionRootImpl() { this.isTopNode() }
}

class BinaryExpressionImpl extends ExpressionNodeImpl {
  BinaryExpressionImpl() {
    this.getKind() = ["OrExpression", "AndExpression", "EqualityExpression", "ComparisonExpression"]
  }

  ExpressionNodeImpl getLeftOperand() { result = this.getChild(0) }

  ExpressionNodeImpl getRightOperand() { result = this.getChild(1) }

  string getOperator() {
    result =
      this.getExpression()
          .getExpression()
          .substring(this.getLeftOperand().getEndOffset(), this.getRightOperand().getStartOffset())
          .trim()
  }
}

class UnaryExpressionImpl extends ExpressionNodeImpl {
  UnaryExpressionImpl() { this.getKind() = "NotExpression" }

  ExpressionNodeImpl getOperand() { result = this.getChild(0) }

  string getOperator() { result = "!" }
}

class IdentifierExpressionImpl extends ExpressionNodeImpl {
  IdentifierExpressionImpl() { this.getKind() = "Identifier" }

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
