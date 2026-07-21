import codeql.actions.Ast

query predicate parseFailures(If guard) { not exists(guard.getConditionExpr().getRoot()) }

query predicate binaryOperands(
  BinaryExpression expression, string operator, string left, string right
) {
  operator = expression.getOperator() and
  left = expression.getLeftOperand().getText() and
  right = expression.getRightOperand().getText()
}

query predicate unaryOperands(UnaryExpression expression, string operator, string operand) {
  operator = expression.getOperator() and operand = expression.getOperand().getText()
}

query predicate callArguments(FunctionCallExpression call, string callee, int index, string argument) {
  callee = call.getCallee().getName() and argument = call.getArgument(index).getText()
}

query predicate accesses(AccessExpression access, string base, string accessor) {
  base = access.getBase().getText() and accessor = access.getAccessor().getText()
}

query predicate properties(PropertyAccessExpression access, string name) { name = access.getName() }

query predicate indexes(IndexAccessExpression access, string index) {
  index = access.getIndex().getText()
}

query predicate literals(LiteralExpression literal, string value) { value = literal.getValue() }
