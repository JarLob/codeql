import codeql.actions.Ast
private import codeql.actions.config.Config

/** Gets the decoded value of the string literal `node`. */
bindingset[node]
pragma[inline_late]
string getStringLiteralValue(ExpressionNode node) {
  node instanceof LiteralExpression and
  node.getKind() = "StringLiteral" and
  result =
    node.(LiteralExpression)
        .getValue()
        .substring(1, node.(LiteralExpression).getValue().length() - 1)
        .regexpReplaceAll("''", "'")
}

private predicate getStringValue(ExpressionNode node, Event event, string value) {
  value = getStringLiteralValue(node)
  or
  node instanceof AccessExpression and
  node.(AccessExpression).getAccessPath() = "github.event_name" and
  value = event.getName()
  or
  node instanceof AccessExpression and
  node.(AccessExpression).getAccessPath() = "github.event.action" and
  value = unique(string activity | activity = event.getAnActivityType())
  or
  isKnownNullValue(node, event) and value = ""
}

private predicate getNumberValue(ExpressionNode node, float value) {
  node instanceof LiteralExpression and
  node.getKind() = "NumberLiteral" and
  value = node.(LiteralExpression).getValue().toFloat()
}

private predicate isNullValue(ExpressionNode node) {
  node instanceof LiteralExpression and node.getKind() = "NullLiteral"
}

private predicate isKnownMissingEventValue(ExpressionNode node, Event event) {
  exists(string path, string contextPrefix |
    node instanceof AccessExpression and
    path = node.(AccessExpression).getAccessPath() and
    contextTriggerDataModel(_, contextPrefix) and
    (path = contextPrefix or path.matches(contextPrefix + ".%")) and
    not contextTriggerDataModel(event.getName(), contextPrefix)
  )
}

private predicate isKnownNullValue(ExpressionNode node, Event event) {
  isNullValue(node) or isKnownMissingEventValue(node, event)
}

private newtype TStatusMode =
  TUnknownStatusMode() or
  TKnownNeedsStatusMode(boolean hasFailure, boolean hasCancellation, boolean hasSkip) {
    hasFailure in [false, true] and
    hasCancellation in [false, true] and
    hasSkip in [false, true]
  }

private TStatusMode unknownStatusMode() { result = TUnknownStatusMode() }

bindingset[status]
private TStatusMode knownNeedsStatusMode(string status) {
  status = "success" and result = TKnownNeedsStatusMode(false, false, false)
  or
  status = "failure" and result = TKnownNeedsStatusMode(true, false, false)
  or
  status = "cancelled" and result = TKnownNeedsStatusMode(false, true, false)
  or
  status = "skipped" and result = TKnownNeedsStatusMode(false, false, true)
}

bindingset[hasFailure, hasCancellation, hasSkip]
private TStatusMode knownNeedsStatusMode(
  boolean hasFailure, boolean hasCancellation, boolean hasSkip
) {
  result = TKnownNeedsStatusMode(hasFailure, hasCancellation, hasSkip)
}

private predicate getKnownNeedsState(
  TStatusMode statusMode, boolean hasFailure, boolean hasCancellation, boolean hasSkip
) {
  statusMode = TKnownNeedsStatusMode(hasFailure, hasCancellation, hasSkip)
}

private predicate getBooleanValue(
  ExpressionNode node, Event event, TStatusMode statusMode, boolean outcome
) {
  node instanceof ExpressionRoot and
  getBooleanValue(node.getAChild(), event, statusMode, outcome)
  or
  node instanceof LiteralExpression and
  node.getKind() = "BooleanLiteral" and
  node.(LiteralExpression).getValue().toLowerCase() = outcome.toString()
  or
  node instanceof UnaryExpression and
  node.(UnaryExpression).getOperator() = "!" and
  exists(boolean operandOutcome |
    evaluatesToBooleanWithStatus(node.(UnaryExpression).getOperand(), event, statusMode,
      operandOutcome) and
    (
      operandOutcome = true and outcome = false
      or
      operandOutcome = false and outcome = true
    )
  )
  or
  node instanceof BinaryExpression and
  evaluateLogical(node.(BinaryExpression), event, statusMode, outcome)
  or
  node instanceof BinaryExpression and
  node.(BinaryExpression).getOperator() = ["==", "!=", ">", ">=", "<", "<="] and
  evaluateEquality(node.(BinaryExpression), event, statusMode, outcome)
  or
  node instanceof FunctionCallExpression and
  evaluateFunctionCall(node.(FunctionCallExpression), event, statusMode, outcome)
}

/**
 * Holds if applying the Boolean comparison `operator` to `left` and `right` evaluates to
 * `outcome`. Unsupported operators yield no result.
 */
bindingset[left, operator, right]
pragma[inline_late]
predicate booleanComparisonEvaluatesTo(
  boolean left, string operator, boolean right, boolean outcome
) {
  operator = "==" and left = right and outcome = true
  or
  operator = "==" and left != right and outcome = false
  or
  operator = "!=" and left != right and outcome = true
  or
  operator = "!=" and left = right and outcome = false
}

/**
 * Holds if applying the case-insensitive string comparison `operator` to `left` and `right`
 * evaluates to `outcome`. Unsupported operators yield no result.
 */
bindingset[left, operator, right]
pragma[inline_late]
predicate stringComparisonEvaluatesTo(
  string left, string operator, string right, boolean outcome
) {
  operator = "==" and left.toLowerCase() = right.toLowerCase() and outcome = true
  or
  operator = "==" and left.toLowerCase() != right.toLowerCase() and outcome = false
  or
  operator = "!=" and left.toLowerCase() != right.toLowerCase() and outcome = true
  or
  operator = "!=" and left.toLowerCase() = right.toLowerCase() and outcome = false
}

/**
 * Holds if applying the numeric comparison `operator` to `left` and `right` evaluates to
 * `outcome`. Unsupported operators yield no result.
 */
bindingset[left, operator, right]
pragma[inline_late]
predicate numericComparisonEvaluatesTo(
  float left, string operator, float right, boolean outcome
) {
  operator = "==" and left = right and outcome = true
  or
  operator = "==" and left != right and outcome = false
  or
  operator = "!=" and left != right and outcome = true
  or
  operator = "!=" and left = right and outcome = false
  or
  operator = ">" and left > right and outcome = true
  or
  operator = ">" and left <= right and outcome = false
  or
  operator = ">=" and left >= right and outcome = true
  or
  operator = ">=" and left < right and outcome = false
  or
  operator = "<" and left < right and outcome = true
  or
  operator = "<" and left >= right and outcome = false
  or
  operator = "<=" and left <= right and outcome = true
  or
  operator = "<=" and left > right and outcome = false
}

/** Holds if the Actions truthiness of the string `value` is `outcome`. */
bindingset[value]
pragma[inline_late]
predicate stringTruthinessEvaluatesTo(string value, boolean outcome) {
  value = "" and outcome = false
  or
  value != "" and outcome = true
}

/** Holds if the Actions truthiness of the number `value` is `outcome`. */
bindingset[value]
pragma[inline_late]
predicate numericTruthinessEvaluatesTo(float value, boolean outcome) {
  value = 0 and outcome = false
  or
  value != 0 and outcome = true
}

/** Holds if comparing two null values with `operator` evaluates to `outcome`. */
bindingset[operator]
pragma[inline_late]
predicate nullComparisonEvaluatesTo(string operator, boolean outcome) {
  operator = "==" and outcome = true
  or
  operator = "!=" and outcome = false
}

private predicate evaluateEquality(
  BinaryExpression expression, Event event, TStatusMode statusMode, boolean outcome
) {
  exists(string left, string right |
    getStringValue(expression.getLeftOperand(), event, left) and
    getStringValue(expression.getRightOperand(), event, right) and
    stringComparisonEvaluatesTo(left, expression.getOperator(), right, outcome)
  )
  or
  exists(boolean left, boolean right |
    getBooleanValue(expression.getLeftOperand(), event, statusMode, left) and
    getBooleanValue(expression.getRightOperand(), event, statusMode, right) and
    booleanComparisonEvaluatesTo(left, expression.getOperator(), right, outcome)
  )
  or
  exists(float left, float right |
    getNumberValue(expression.getLeftOperand(), left) and
    getNumberValue(expression.getRightOperand(), right) and
    numericComparisonEvaluatesTo(left, expression.getOperator(), right, outcome)
  )
  or
  isKnownNullValue(expression.getLeftOperand(), event) and
  isKnownNullValue(expression.getRightOperand(), event) and
  nullComparisonEvaluatesTo(expression.getOperator(), outcome)
}

private predicate logicalOperandEvaluatesTo(
  BinaryExpression expression, int index, Event event, TStatusMode statusMode, boolean outcome
) {
  index = 0 and
  evaluatesToBooleanWithStatus(expression.getLeftOperand(), event, statusMode, outcome)
  or
  index = 1 and
  evaluatesToBooleanWithStatus(expression.getRightOperand(), event, statusMode, outcome)
}

private predicate evaluateLogical(
  BinaryExpression expression, Event event, TStatusMode statusMode, boolean outcome
) {
  expression.getOperator() = "&&" and
  outcome = false and
  logicalOperandEvaluatesTo(expression, _, event, statusMode, false)
  or
  expression.getOperator() = "&&" and
  outcome = true and
  logicalOperandEvaluatesTo(expression, 0, event, statusMode, true) and
  logicalOperandEvaluatesTo(expression, 1, event, statusMode, true)
  or
  expression.getOperator() = "||" and
  outcome = true and
  logicalOperandEvaluatesTo(expression, _, event, statusMode, true)
  or
  expression.getOperator() = "||" and
  outcome = false and
  logicalOperandEvaluatesTo(expression, 0, event, statusMode, false) and
  logicalOperandEvaluatesTo(expression, 1, event, statusMode, false)
}

bindingset[call, left, right]
private predicate stringFunctionHolds(FunctionCallExpression call, string left, string right) {
  call.getCallee().getName().toLowerCase() = "contains" and
  exists(left.toLowerCase().indexOf(right.toLowerCase()))
  or
  call.getCallee().getName().toLowerCase() = "startswith" and
  left.toLowerCase().indexOf(right.toLowerCase()) = 0
  or
  call.getCallee().getName().toLowerCase() = "endswith" and
  left.length() >= right.length() and
  left.toLowerCase().suffix(left.length() - right.length()) = right.toLowerCase()
}

private predicate evaluateFunctionCall(
  FunctionCallExpression call, Event event, TStatusMode statusMode, boolean outcome
) {
  call.getCallee().getName().toLowerCase() = "always" and
  not exists(call.getArgument(_)) and
  outcome = true
  or
  exists(boolean hasFailure, boolean hasCancellation, boolean hasSkip |
    getKnownNeedsState(statusMode, hasFailure, hasCancellation, hasSkip) and
    call.getCallee().getName().toLowerCase() = ["success", "failure", "cancelled"] and
    not exists(call.getArgument(_)) and
    (
      call.getCallee().getName().toLowerCase() = "success" and
      hasFailure = false and
      hasCancellation = false and
      hasSkip = false and
      outcome = true
      or
      call.getCallee().getName().toLowerCase() = "success" and
      (hasFailure = true or hasCancellation = true or hasSkip = true) and
      outcome = false
      or
      call.getCallee().getName().toLowerCase() = "failure" and outcome = hasFailure
      or
      call.getCallee().getName().toLowerCase() = "cancelled" and outcome = hasCancellation
    )
  )
  or
  exists(string left, string right |
    getStringValue(call.getArgument(0), event, left) and
    getStringValue(call.getArgument(1), event, right) and
    (
      stringFunctionHolds(call, left, right) and outcome = true
      or
      call.getCallee().getName().toLowerCase() = ["contains", "startswith", "endswith"] and
      not stringFunctionHolds(call, left, right) and
      outcome = false
    )
  )
}

// Keep condition evaluation in a separate recursive component so production callers do not
// materialize evaluation results for expression trees that cannot control execution.
private predicate conditionGetBooleanValue(
  If condition, ExpressionNode node, Event event, TStatusMode statusMode, boolean outcome
) {
  condition.getConditionExpr() = node.getExpression() and
  (
    node instanceof ExpressionRoot and
    conditionGetBooleanValue(condition, node.getAChild(), event, statusMode, outcome)
    or
    node instanceof LiteralExpression and
    node.getKind() = "BooleanLiteral" and
    node.(LiteralExpression).getValue().toLowerCase() = outcome.toString()
    or
    node instanceof UnaryExpression and
    node.(UnaryExpression).getOperator() = "!" and
    exists(boolean operandOutcome |
      conditionEvaluatesToBooleanWithStatus(condition, node.(UnaryExpression).getOperand(), event,
        statusMode, operandOutcome) and
      (
        operandOutcome = true and outcome = false
        or
        operandOutcome = false and outcome = true
      )
    )
    or
    node instanceof BinaryExpression and
    conditionEvaluateLogical(condition, node.(BinaryExpression), event, statusMode, outcome)
    or
    node instanceof BinaryExpression and
    node.(BinaryExpression).getOperator() = ["==", "!=", ">", ">=", "<", "<="] and
    conditionEvaluateEquality(condition, node.(BinaryExpression), event, statusMode, outcome)
    or
    node instanceof FunctionCallExpression and
    evaluateFunctionCall(node.(FunctionCallExpression), event, statusMode, outcome)
  )
}

private predicate conditionEvaluateEquality(
  If condition, BinaryExpression expression, Event event, TStatusMode statusMode, boolean outcome
) {
  condition.getConditionExpr() = expression.getExpression() and
  (
    exists(string left, string right |
      conditionEqualityStringOperand(expression, 0, event, left) and
      conditionEqualityStringOperand(expression, 1, event, right) and
      stringComparisonEvaluatesTo(left, expression.getOperator(), right, outcome)
    )
    or
    exists(boolean left, boolean right |
      conditionEqualityBooleanOperand(condition, expression, 0, event, statusMode, left) and
      conditionEqualityBooleanOperand(condition, expression, 1, event, statusMode, right) and
      booleanComparisonEvaluatesTo(left, expression.getOperator(), right, outcome)
    )
    or
    exists(float left, float right |
      conditionEqualityNumberOperand(expression, 0, left) and
      conditionEqualityNumberOperand(expression, 1, right) and
      numericComparisonEvaluatesTo(left, expression.getOperator(), right, outcome)
    )
    or
    conditionEqualityOperandIsKnownNull(expression, 0, event) and
    conditionEqualityOperandIsKnownNull(expression, 1, event) and
    nullComparisonEvaluatesTo(expression.getOperator(), outcome)
  )
}

// Keep operand values keyed by their comparison before combining event-specific values.
private predicate conditionEqualityStringOperand(
  BinaryExpression expression, int index, Event event, string value
) {
  (
    index = 0 and getStringValue(expression.getLeftOperand(), event, value)
    or
    index = 1 and getStringValue(expression.getRightOperand(), event, value)
  )
}

private predicate conditionEqualityBooleanOperand(
  If condition, BinaryExpression expression, int index, Event event, TStatusMode statusMode,
  boolean outcome
) {
  (
    index = 0 and
    conditionGetBooleanValue(condition, expression.getLeftOperand(), event, statusMode, outcome)
    or
    index = 1 and
    conditionGetBooleanValue(condition, expression.getRightOperand(), event, statusMode, outcome)
  )
}

private predicate conditionEqualityNumberOperand(BinaryExpression expression, int index, float value) {
  (
    index = 0 and getNumberValue(expression.getLeftOperand(), value)
    or
    index = 1 and getNumberValue(expression.getRightOperand(), value)
  )
}

private predicate conditionEqualityOperandIsKnownNull(
  BinaryExpression expression, int index, Event event
) {
  (
    index = 0 and isKnownNullValue(expression.getLeftOperand(), event)
    or
    index = 1 and isKnownNullValue(expression.getRightOperand(), event)
  )
}

private predicate conditionLogicalOperandEvaluatesTo(
  If condition, BinaryExpression expression, int index, Event event, TStatusMode statusMode,
  boolean outcome
) {
  condition.getConditionExpr() = expression.getExpression() and
  index = 0 and
  conditionEvaluatesToBooleanWithStatus(condition, expression.getLeftOperand(), event, statusMode,
    outcome)
  or
  condition.getConditionExpr() = expression.getExpression() and
  index = 1 and
  conditionEvaluatesToBooleanWithStatus(condition, expression.getRightOperand(), event, statusMode,
    outcome)
}

private predicate conditionEvaluateLogical(
  If condition, BinaryExpression expression, Event event, TStatusMode statusMode, boolean outcome
) {
  condition.getConditionExpr() = expression.getExpression() and
  expression.getOperator() = "&&" and
  outcome = false and
  conditionLogicalOperandEvaluatesTo(condition, expression, _, event, statusMode, false)
  or
  condition.getConditionExpr() = expression.getExpression() and
  expression.getOperator() = "&&" and
  outcome = true and
  conditionLogicalOperandEvaluatesTo(condition, expression, 0, event, statusMode, true) and
  conditionLogicalOperandEvaluatesTo(condition, expression, 1, event, statusMode, true)
  or
  condition.getConditionExpr() = expression.getExpression() and
  expression.getOperator() = "||" and
  outcome = true and
  conditionLogicalOperandEvaluatesTo(condition, expression, _, event, statusMode, true)
  or
  condition.getConditionExpr() = expression.getExpression() and
  expression.getOperator() = "||" and
  outcome = false and
  conditionLogicalOperandEvaluatesTo(condition, expression, 0, event, statusMode, false) and
  conditionLogicalOperandEvaluatesTo(condition, expression, 1, event, statusMode, false)
}

private predicate conditionEvaluatesToBooleanWithStatus(
  If condition, ExpressionNode node, Event event, TStatusMode statusMode, boolean outcome
) {
  condition.getConditionExpr() = node.getExpression() and
  (
    condition.getATriggerEvent() = event
    or
    not exists(condition.getATriggerEvent())
  ) and
  (
    conditionGetBooleanValue(condition, node, event, statusMode, outcome)
    or
    isKnownNullValue(node, event) and outcome = false
    or
    exists(string value | getStringValue(node, event, value) |
      stringTruthinessEvaluatesTo(value, outcome)
    )
    or
    exists(float value | getNumberValue(node, value) |
      numericTruthinessEvaluatesTo(value, outcome)
    )
  )
}

private predicate conditionMayEvaluateToBooleanWithStatus(
  If condition, ExpressionNode node, Event event, TStatusMode statusMode, boolean outcome
) {
  condition.getConditionExpr() = node.getExpression() and
  (
    condition.getATriggerEvent() = event
    or
    not exists(condition.getATriggerEvent())
  ) and
  (
    conditionEvaluatesToBooleanWithStatus(condition, node, event, statusMode, outcome)
    or
    outcome in [false, true] and
    not exists(boolean known |
      conditionEvaluatesToBooleanWithStatus(condition, node, event, statusMode, known)
    )
  )
}

bindingset[node, combination]
pragma[inline_late]
private predicate getMatrixScalarValue(
  ExpressionNode node, MatrixCombination combination, string kind, string value
) {
  exists(AccessExpression access, string path, string accessPath |
    access = node and
    path = access.getAccessPath() and
    path.toLowerCase().matches("matrix.%") and
    accessPath = path.suffix("matrix.".length()) and
    kind = combination.getValueKind(accessPath) and
    value = combination.getValue(accessPath)
  )
}

private predicate matrixGetStringValue(
  ExpressionNode node, Event event, MatrixCombination combination, string value
) {
  getStringValue(node, event, value)
  or
  getMatrixScalarValue(node, combination, "StringLiteral", value)
}

private predicate matrixGetNumberValue(
  ExpressionNode node, MatrixCombination combination, float value
) {
  getNumberValue(node, value)
  or
  exists(string raw |
    getMatrixScalarValue(node, combination, "NumberLiteral", raw) and value = raw.toFloat()
  )
}

private predicate matrixIsKnownNullValue(
  ExpressionNode node, Event event, MatrixCombination combination
) {
  isKnownNullValue(node, event)
  or
  exists(string value | getMatrixScalarValue(node, combination, "NullLiteral", value))
}

private predicate matrixGetBooleanValue(
  ExpressionNode node, Event event, TStatusMode statusMode, MatrixCombination combination,
  boolean outcome
) {
  getBooleanValue(node, event, statusMode, outcome)
  or
  exists(string raw |
    getMatrixScalarValue(node, combination, "BooleanLiteral", raw) and
    raw.toLowerCase() = outcome.toString()
  )
  or
  node instanceof ExpressionRoot and
  matrixGetBooleanValue(node.getAChild(), event, statusMode, combination, outcome)
  or
  node instanceof UnaryExpression and
  node.(UnaryExpression).getOperator() = "!" and
  exists(boolean operandOutcome |
    matrixEvaluatesToBooleanWithStatus(node.(UnaryExpression).getOperand(), event, statusMode,
      combination, operandOutcome) and
    (
      operandOutcome = true and outcome = false
      or
      operandOutcome = false and outcome = true
    )
  )
  or
  node instanceof BinaryExpression and
  matrixEvaluateLogical(node.(BinaryExpression), event, statusMode, combination, outcome)
  or
  node instanceof BinaryExpression and
  node.(BinaryExpression).getOperator() = ["==", "!=", ">", ">=", "<", "<="] and
  matrixEvaluateEquality(node.(BinaryExpression), event, statusMode, combination, outcome)
  or
  node instanceof FunctionCallExpression and
  matrixEvaluateFunctionCall(node.(FunctionCallExpression), event, statusMode, combination,
    outcome)
}

private predicate matrixEvaluateEquality(
  BinaryExpression expression, Event event, TStatusMode statusMode,
  MatrixCombination combination, boolean outcome
) {
  exists(string left, string right |
    matrixGetStringValue(expression.getLeftOperand(), event, combination, left) and
    matrixGetStringValue(expression.getRightOperand(), event, combination, right) and
    stringComparisonEvaluatesTo(left, expression.getOperator(), right, outcome)
  )
  or
  exists(boolean left, boolean right |
    matrixGetBooleanValue(expression.getLeftOperand(), event, statusMode, combination, left) and
    matrixGetBooleanValue(expression.getRightOperand(), event, statusMode, combination, right) and
    booleanComparisonEvaluatesTo(left, expression.getOperator(), right, outcome)
  )
  or
  exists(float left, float right |
    matrixGetNumberValue(expression.getLeftOperand(), combination, left) and
    matrixGetNumberValue(expression.getRightOperand(), combination, right) and
    numericComparisonEvaluatesTo(left, expression.getOperator(), right, outcome)
  )
  or
  matrixIsKnownNullValue(expression.getLeftOperand(), event, combination) and
  matrixIsKnownNullValue(expression.getRightOperand(), event, combination) and
  nullComparisonEvaluatesTo(expression.getOperator(), outcome)
}

private predicate matrixLogicalOperandEvaluatesTo(
  BinaryExpression expression, int index, Event event, TStatusMode statusMode,
  MatrixCombination combination, boolean outcome
) {
  index = 0 and
  matrixEvaluatesToBooleanWithStatus(expression.getLeftOperand(), event, statusMode, combination,
    outcome)
  or
  index = 1 and
  matrixEvaluatesToBooleanWithStatus(expression.getRightOperand(), event, statusMode, combination,
    outcome)
}

private predicate matrixEvaluateLogical(
  BinaryExpression expression, Event event, TStatusMode statusMode,
  MatrixCombination combination, boolean outcome
) {
  expression.getOperator() = "&&" and
  outcome = false and
  matrixLogicalOperandEvaluatesTo(expression, _, event, statusMode, combination, false)
  or
  expression.getOperator() = "&&" and
  outcome = true and
  matrixLogicalOperandEvaluatesTo(expression, 0, event, statusMode, combination, true) and
  matrixLogicalOperandEvaluatesTo(expression, 1, event, statusMode, combination, true)
  or
  expression.getOperator() = "||" and
  outcome = true and
  matrixLogicalOperandEvaluatesTo(expression, _, event, statusMode, combination, true)
  or
  expression.getOperator() = "||" and
  outcome = false and
  matrixLogicalOperandEvaluatesTo(expression, 0, event, statusMode, combination, false) and
  matrixLogicalOperandEvaluatesTo(expression, 1, event, statusMode, combination, false)
}

private predicate matrixEvaluateFunctionCall(
  FunctionCallExpression call, Event event, TStatusMode statusMode,
  MatrixCombination combination, boolean outcome
) {
  evaluateFunctionCall(call, event, statusMode, outcome)
  or
  exists(string left, string right |
    matrixGetStringValue(call.getArgument(0), event, combination, left) and
    matrixGetStringValue(call.getArgument(1), event, combination, right) and
    (
      stringFunctionHolds(call, left, right) and outcome = true
      or
      call.getCallee().getName().toLowerCase() = ["contains", "startswith", "endswith"] and
      not stringFunctionHolds(call, left, right) and
      outcome = false
    )
  )
}

private predicate matrixEvaluatesToBooleanWithStatus(
  ExpressionNode node, Event event, TStatusMode statusMode, MatrixCombination combination,
  boolean outcome
) {
  (
    node.getExpression().getATriggerEvent() = event
    or
    not exists(node.getExpression().getATriggerEvent())
  ) and
  (
    matrixGetBooleanValue(node, event, statusMode, combination, outcome)
    or
    matrixIsKnownNullValue(node, event, combination) and outcome = false
    or
    exists(string value | matrixGetStringValue(node, event, combination, value) |
      stringTruthinessEvaluatesTo(value, outcome)
    )
    or
    exists(float value | matrixGetNumberValue(node, combination, value) |
      numericTruthinessEvaluatesTo(value, outcome)
    )
  )
}

private predicate matrixMayEvaluateToBooleanWithStatus(
  ExpressionNode node, Event event, TStatusMode statusMode, MatrixCombination combination,
  boolean outcome
) {
  matrixEvaluatesToBooleanWithStatus(node, event, statusMode, combination, outcome)
  or
  outcome in [false, true] and
  not exists(boolean known |
    matrixEvaluatesToBooleanWithStatus(node, event, statusMode, combination, known)
  )
}

private ExpressionNode getMatrixEvaluationNode(ExpressionNode node) {
  node instanceof ExpressionRoot and result = node.getAChild()
  or
  not node instanceof ExpressionRoot and result = node
}

/** Holds if `node` is known to evaluate to `outcome` for this matrix combination. */
predicate evaluatesToBooleanForMatrixCombination(
  ExpressionNode node, Event event, MatrixCombination combination, boolean outcome
) {
  matrixEvaluatesToBooleanWithStatus(getMatrixEvaluationNode(node), event, unknownStatusMode(),
    combination, outcome)
}

/** Holds if `node` may evaluate to `outcome` for this matrix combination. */
predicate mayEvaluateToBooleanForMatrixCombination(
  ExpressionNode node, Event event, MatrixCombination combination, boolean outcome
) {
  matrixMayEvaluateToBooleanWithStatus(getMatrixEvaluationNode(node), event, unknownStatusMode(),
    combination, outcome)
}

/** Holds if `condition` may evaluate to `outcome` for this matrix combination. */
predicate mayEvaluateConditionToBooleanForMatrixCombination(
  If condition, ExpressionNode node, Event event, MatrixCombination combination, boolean outcome
) {
  condition.getConditionExpr() = node.getExpression() and
  matrixMayEvaluateToBooleanWithStatus(getMatrixEvaluationNode(node), event, unknownStatusMode(),
    combination, outcome)
}

/** Holds if `condition` may permit this matrix combination to execute. */
predicate isConditionFeasibleForMatrixCombination(
  If condition, Event event, MatrixCombination combination
) {
  mayEvaluateConditionToBooleanForMatrixCombination(condition,
    condition.getConditionExpr().getRoot(), event, combination, true)
}

/** Holds if `node` may evaluate to `outcome` for a matrix combination and needs state. */
bindingset[hasFailure, hasCancellation, hasSkip]
pragma[inline_late]
predicate mayEvaluateToBooleanForMatrixCombinationAfterNeedsState(
  ExpressionNode node, Event event, MatrixCombination combination, boolean hasFailure,
  boolean hasCancellation, boolean hasSkip, boolean outcome
) {
  matrixMayEvaluateToBooleanWithStatus(getMatrixEvaluationNode(node), event,
    knownNeedsStatusMode(hasFailure, hasCancellation, hasSkip), combination, outcome)
}

/** Holds if `node` is known to evaluate to `outcome` for a matrix combination and needs state. */
bindingset[hasFailure, hasCancellation, hasSkip]
pragma[inline_late]
predicate evaluatesToBooleanForMatrixCombinationAfterNeedsState(
  ExpressionNode node, Event event, MatrixCombination combination, boolean hasFailure,
  boolean hasCancellation, boolean hasSkip, boolean outcome
) {
  matrixEvaluatesToBooleanWithStatus(getMatrixEvaluationNode(node), event,
    knownNeedsStatusMode(hasFailure, hasCancellation, hasSkip), combination, outcome)
}

/** Holds if `condition` may evaluate to `outcome` for a matrix combination and needs state. */
bindingset[hasFailure, hasCancellation, hasSkip]
pragma[inline_late]
predicate mayEvaluateConditionToBooleanForMatrixCombinationAfterNeedsState(
  If condition, ExpressionNode node, Event event, MatrixCombination combination,
  boolean hasFailure, boolean hasCancellation, boolean hasSkip, boolean outcome
) {
  condition.getConditionExpr() = node.getExpression() and
  matrixMayEvaluateToBooleanWithStatus(getMatrixEvaluationNode(node), event,
    knownNeedsStatusMode(hasFailure, hasCancellation, hasSkip), combination, outcome)
}

/**
 * Holds if `node` is known to evaluate to the Boolean value `result` for `event`.
 * Absence of a result means that the value is unknown.
 */
predicate evaluatesToBoolean(ExpressionNode node, Event event, boolean outcome) {
  evaluatesToBooleanWithStatus(node, event, unknownStatusMode(), outcome)
}

private predicate evaluatesToBooleanWithStatus(
  ExpressionNode node, Event event, TStatusMode statusMode, boolean outcome
) {
  (
    node.getExpression().getATriggerEvent() = event
    or
    not exists(node.getExpression().getATriggerEvent())
  ) and
  (
    getBooleanValue(node, event, statusMode, outcome)
    or
    isKnownNullValue(node, event) and outcome = false
    or
    exists(string value | getStringValue(node, event, value) |
      stringTruthinessEvaluatesTo(value, outcome)
    )
    or
    exists(float value | getNumberValue(node, value) |
      numericTruthinessEvaluatesTo(value, outcome)
    )
  )
}

/** Holds if `node` may evaluate to `result` for `event`. */
predicate mayEvaluateToBoolean(ExpressionNode node, Event event, boolean outcome) {
  mayEvaluateToBooleanWithStatus(node, event, unknownStatusMode(), outcome)
}

private predicate mayEvaluateToBooleanWithStatus(
  ExpressionNode node, Event event, TStatusMode statusMode, boolean outcome
) {
  (
    node.getExpression().getATriggerEvent() = event
    or
    not exists(node.getExpression().getATriggerEvent())
  ) and
  (
    evaluatesToBooleanWithStatus(node, event, statusMode, outcome)
    or
    outcome in [false, true] and
    not exists(boolean known | evaluatesToBooleanWithStatus(node, event, statusMode, known))
  )
}

private predicate accessesWorkflowRunSourceEvent(ExpressionNode node) {
  node instanceof AccessExpression and
  node.(AccessExpression).getAccessPath() = "github.event.workflow_run.event"
}

private predicate containsWorkflowRunSourceEventAccess(ExpressionNode node) {
  accessesWorkflowRunSourceEvent(node.getAChild*())
}

private predicate getWorkflowRunSourceStringValue(
  ExpressionNode node, Event event, Event sourceEvent, string value
) {
  value = getStringLiteralValue(node)
  or
  node instanceof AccessExpression and
  node.(AccessExpression).getAccessPath() = "github.event_name" and
  value = event.getName()
  or
  node instanceof AccessExpression and
  node.(AccessExpression).getAccessPath() = "github.event.action" and
  value = unique(string activity | activity = event.getAnActivityType())
  or
  accessesWorkflowRunSourceEvent(node) and
  event.getName() = "workflow_run" and
  value = sourceEvent.getName()
}

private predicate evaluateWorkflowRunSourceFunctionCall(
  FunctionCallExpression call, Event event, Event sourceEvent, boolean outcome
) {
  not containsWorkflowRunSourceEventAccess(call) and
  evaluatesToBoolean(call, event, outcome)
  or
  exists(string left, string right |
    getWorkflowRunSourceStringValue(call.getArgument(0), event, sourceEvent, left) and
    getWorkflowRunSourceStringValue(call.getArgument(1), event, sourceEvent, right) and
    (
      stringFunctionHolds(call, left, right) and outcome = true
      or
      call.getCallee().getName().toLowerCase() = ["contains", "startswith", "endswith"] and
      not stringFunctionHolds(call, left, right) and
      outcome = false
    )
  )
}

private predicate evaluateWorkflowRunSourceEquality(
  BinaryExpression expression, Event event, Event sourceEvent, boolean outcome
) {
  exists(string left, string right |
    getWorkflowRunSourceStringValue(expression.getLeftOperand(), event, sourceEvent, left) and
    getWorkflowRunSourceStringValue(expression.getRightOperand(), event, sourceEvent, right) and
    stringComparisonEvaluatesTo(left, expression.getOperator(), right, outcome)
  )
  or
  exists(boolean left, boolean right |
    evaluatesToBoolean(expression.getLeftOperand(), event, sourceEvent, left) and
    evaluatesToBoolean(expression.getRightOperand(), event, sourceEvent, right) and
    booleanComparisonEvaluatesTo(left, expression.getOperator(), right, outcome)
  )
}

private predicate workflowRunSourceLogicalOperandEvaluatesTo(
  BinaryExpression expression, int index, Event event, Event sourceEvent, boolean outcome
) {
  index = 0 and
  evaluatesToBoolean(expression.getLeftOperand(), event, sourceEvent, outcome)
  or
  index = 1 and
  evaluatesToBoolean(expression.getRightOperand(), event, sourceEvent, outcome)
}

private predicate evaluateWorkflowRunSourceLogical(
  BinaryExpression expression, Event event, Event sourceEvent, boolean outcome
) {
  expression.getOperator() = "&&" and
  outcome = false and
  workflowRunSourceLogicalOperandEvaluatesTo(expression, _, event, sourceEvent, false)
  or
  expression.getOperator() = "&&" and
  outcome = true and
  workflowRunSourceLogicalOperandEvaluatesTo(expression, 0, event, sourceEvent, true) and
  workflowRunSourceLogicalOperandEvaluatesTo(expression, 1, event, sourceEvent, true)
  or
  expression.getOperator() = "||" and
  outcome = true and
  workflowRunSourceLogicalOperandEvaluatesTo(expression, _, event, sourceEvent, true)
  or
  expression.getOperator() = "||" and
  outcome = false and
  workflowRunSourceLogicalOperandEvaluatesTo(expression, 0, event, sourceEvent, false) and
  workflowRunSourceLogicalOperandEvaluatesTo(expression, 1, event, sourceEvent, false)
}

/** Holds if `node` is known to evaluate to `outcome` for this workflow-run source event. */
predicate evaluatesToBoolean(ExpressionNode node, Event event, Event sourceEvent, boolean outcome) {
  event.getName() = "workflow_run" and
  event.getALocalWorkflowRunSourceEvent() = sourceEvent and
  (
    not containsWorkflowRunSourceEventAccess(node) and
    evaluatesToBoolean(node, event, outcome)
    or
    node instanceof ExpressionRoot and
    evaluatesToBoolean(node.getAChild(), event, sourceEvent, outcome)
    or
    node instanceof UnaryExpression and
    node.(UnaryExpression).getOperator() = "!" and
    exists(boolean operandOutcome |
      evaluatesToBoolean(node.(UnaryExpression).getOperand(), event, sourceEvent, operandOutcome) and
      (
        operandOutcome = true and outcome = false
        or
        operandOutcome = false and outcome = true
      )
    )
    or
    node instanceof BinaryExpression and
    node.(BinaryExpression).getOperator() = ["&&", "||"] and
    evaluateWorkflowRunSourceLogical(node.(BinaryExpression), event, sourceEvent, outcome)
    or
    node instanceof BinaryExpression and
    node.(BinaryExpression).getOperator() = ["==", "!="] and
    evaluateWorkflowRunSourceEquality(node.(BinaryExpression), event, sourceEvent, outcome)
    or
    node instanceof FunctionCallExpression and
    evaluateWorkflowRunSourceFunctionCall(node.(FunctionCallExpression), event, sourceEvent, outcome)
  )
}

/** Holds if `node` may evaluate to `outcome` for this workflow-run source event. */
predicate mayEvaluateToBoolean(ExpressionNode node, Event event, Event sourceEvent, boolean outcome) {
  evaluatesToBoolean(node, event, sourceEvent, outcome)
  or
  outcome in [false, true] and
  not exists(boolean known | evaluatesToBoolean(node, event, sourceEvent, known))
}

/** Holds if `node` can be evaluated while `condition` runs for this source event. */
predicate mayEvaluateConditionNode(If condition, ExpressionNode node, Event event, Event sourceEvent) {
  condition.getConditionExpr() = node.getExpression() and
  event.getName() = "workflow_run" and
  event.getALocalWorkflowRunSourceEvent() = sourceEvent and
  (
    node = condition.getConditionExpr().getRoot()
    or
    exists(ExpressionRoot root |
      node = root.getAChild() and
      mayEvaluateConditionNode(condition, root, event, sourceEvent)
    )
    or
    exists(UnaryExpression unary |
      node = unary.getOperand() and
      mayEvaluateConditionNode(condition, unary, event, sourceEvent)
    )
    or
    exists(BinaryExpression binary |
      binary.getOperator() = ["&&", "||"] and
      (
        node = binary.getLeftOperand() and
        mayEvaluateConditionNode(condition, binary, event, sourceEvent)
        or
        node = binary.getRightOperand() and
        mayEvaluateConditionNode(condition, binary, event, sourceEvent) and
        (
          binary.getOperator() = "&&" and
          mayEvaluateToBoolean(binary.getLeftOperand(), event, sourceEvent, true)
          or
          binary.getOperator() = "||" and
          mayEvaluateToBoolean(binary.getLeftOperand(), event, sourceEvent, false)
        )
      )
    )
  )
}

/** Holds if `condition` may permit execution for this workflow-run source event. */
predicate isConditionFeasible(If condition, Event event, Event sourceEvent) {
  condition.getATriggerEvent() = event and
  event.getName() = "workflow_run" and
  event.getALocalWorkflowRunSourceEvent() = sourceEvent and
  not evaluatesToBoolean(condition.getConditionExpr().getRoot(), event, sourceEvent, false)
}

/** Holds if the condition may permit execution for `event`. */
predicate isConditionFeasible(If condition, Event event) {
  not conditionEvaluatesToBooleanWithStatus(condition, condition.getConditionExpr().getRoot(),
    event, unknownStatusMode(), false)
}

/** Holds if `node` may evaluate to `outcome` within `condition` for `event`. */
predicate mayEvaluateConditionToBoolean(
  If condition, ExpressionNode node, Event event, boolean outcome
) {
  conditionMayEvaluateToBooleanWithStatus(condition, node, event, unknownStatusMode(), outcome)
}

/** Holds if the condition may permit execution after a prerequisite job was skipped. */
predicate isConditionFeasibleAfterSkippedNeeds(If condition, Event event) {
  isConditionFeasibleAfterNeedsStatus(condition, event, "skipped")
}

/**
 * Holds if `node` is known to evaluate to `outcome` for a prerequisite-status summary.
 */
bindingset[hasFailure, hasCancellation, hasSkip]
predicate evaluatesToBooleanAfterNeedsState(
  ExpressionNode node, Event event, boolean hasFailure, boolean hasCancellation, boolean hasSkip,
  boolean outcome
) {
  evaluatesToBooleanWithStatus(node, event,
    knownNeedsStatusMode(hasFailure, hasCancellation, hasSkip), outcome)
}

/** Holds if `node` may evaluate to `outcome` for a prerequisite-status summary. */
bindingset[hasFailure, hasCancellation, hasSkip]
predicate mayEvaluateToBooleanAfterNeedsState(
  ExpressionNode node, Event event, boolean hasFailure, boolean hasCancellation, boolean hasSkip,
  boolean outcome
) {
  mayEvaluateToBooleanWithStatus(node, event,
    knownNeedsStatusMode(hasFailure, hasCancellation, hasSkip), outcome)
}

/** Holds if a condition node may evaluate to `outcome` for a prerequisite-status summary. */
bindingset[hasFailure, hasCancellation, hasSkip]
predicate mayEvaluateConditionToBooleanAfterNeedsState(
  If condition, ExpressionNode node, Event event, boolean hasFailure, boolean hasCancellation,
  boolean hasSkip, boolean outcome
) {
  conditionMayEvaluateToBooleanWithStatus(condition, node, event,
    knownNeedsStatusMode(hasFailure, hasCancellation, hasSkip), outcome)
}

/**
 * Holds if `node` is known to evaluate to `outcome` for `event` after prerequisite jobs have the
 * aggregate conclusion `status`.
 */
bindingset[status]
predicate evaluatesToBooleanAfterNeedsStatus(
  ExpressionNode node, Event event, string status, boolean outcome
) {
  evaluatesToBooleanWithStatus(node, event, knownNeedsStatusMode(status), outcome)
}

/** Holds if `node` may evaluate to `outcome` for a known aggregate prerequisite conclusion. */
bindingset[status]
predicate mayEvaluateToBooleanAfterNeedsStatus(
  ExpressionNode node, Event event, string status, boolean outcome
) {
  mayEvaluateToBooleanWithStatus(node, event, knownNeedsStatusMode(status), outcome)
}

/** Holds if the condition may permit execution for a known aggregate prerequisite conclusion. */
bindingset[status]
predicate isConditionFeasibleAfterNeedsStatus(If condition, Event event, string status) {
  conditionMayEvaluateToBooleanWithStatus(condition, condition.getConditionExpr().getRoot(), event,
    knownNeedsStatusMode(status), true)
}

/** Holds if the condition contains a status-check function. */
predicate hasStatusCheckFunction(If condition) {
  exists(FunctionCallExpression call |
    call.getExpression() = condition.getConditionExpr() and
    call.getCallee().getName().toLowerCase() = ["always", "cancelled", "failure", "success"]
  )
}
