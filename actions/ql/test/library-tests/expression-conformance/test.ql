import codeql.actions.Ast
import codeql.actions.ast.internal.ExpressionParserCore as ParserCore

bindingset[length]
private string repeatedA(int length) {
  result = concat(int i | i in [1 .. length] | "a", "" order by i)
}

private string expectedOutcome(Step test) {
  test.getId().matches("valid-%") and result = "parsed"
  or
  test.getId().matches("invalid-%") and result = "rejected"
}

private string actualOutcome(Step test) {
  exists(test.getIf().getConditionExpr().getRoot()) and result = "parsed"
  or
  not exists(test.getIf().getConditionExpr().getRoot()) and result = "rejected"
}

private Step getConformanceStep(ExpressionNode node) {
  result.getIf().getConditionExpr() = node.getExpression()
}

query predicate mismatches(Step test, string expected, string actual) {
  expected = expectedOutcome(test) and
  actual = actualOutcome(test) and
  expected != actual
}

query predicate binaryShapes(
  string caseId, BinaryExpression binary, string operator, string left, string right
) {
  caseId = getConformanceStep(binary).getId() and
  caseId.matches("valid-%") and
  operator = binary.getOperator() and
  left = binary.getLeftOperand().getText() and
  right = binary.getRightOperand().getText()
}

query predicate unaryShapes(string caseId, UnaryExpression unary, string operand) {
  caseId = getConformanceStep(unary).getId() and
  caseId.matches("valid-%") and
  operand = unary.getOperand().getText()
}

query predicate callShapes(
  string caseId, FunctionCallExpression call, string callee, int index, string argument
) {
  caseId = getConformanceStep(call).getId() and
  caseId.matches("valid-%") and
  callee = call.getCallee().getName() and
  argument = call.getArgument(index).getText()
}

query predicate zeroArgumentCalls(string caseId, FunctionCallExpression call, string callee) {
  caseId = getConformanceStep(call).getId() and
  caseId.matches("valid-%") and
  callee = call.getCallee().getName() and
  not exists(call.getArgument(_))
}

query predicate accessShapes(string caseId, AccessExpression access, string base, string accessor) {
  caseId = getConformanceStep(access).getId() and
  caseId.matches("valid-%") and
  base = access.getBase().getText() and
  accessor = access.getAccessor().getText()
}

query predicate literalShapes(string caseId, LiteralExpression literal, string kind, string value) {
  caseId = getConformanceStep(literal).getId() and
  caseId.matches("valid-%") and
  kind = literal.getKind() and
  value = literal.getValue()
}

query predicate roots(string caseId, string kind, string text) {
  exists(ExpressionRoot root |
    caseId = getConformanceStep(root).getId() and
    caseId.matches("valid-%") and
    kind = root.getChild(0).getKind() and
    text = root.getChild(0).getText()
  )
}

query predicate lengthLimits(int length, string outcome) {
  length in [21000, 21001] and
  (
    ParserCore::expressionLengthIsValid(repeatedA(length)) and outcome = "accepted"
    or
    not ParserCore::expressionLengthIsValid(repeatedA(length)) and outcome = "rejected"
  )
}
