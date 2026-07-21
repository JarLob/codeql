import codeql.actions.Ast
private import codeql.actions.config.Config

private predicate getStringLiteralValue(ExpressionNode node, string value) {
  node instanceof LiteralExpression and
  node.getKind() = "StringLiteral" and
  value =
    node.(LiteralExpression)
        .getValue()
        .substring(1, node.(LiteralExpression).getValue().length() - 1)
        .regexpReplaceAll("''", "'")
}

private predicate getStringValue(ExpressionNode node, Event event, string value) {
  getStringLiteralValue(node, value)
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

bindingset[left, operator, right]
private predicate compareBooleans(boolean left, string operator, boolean right, boolean outcome) {
  operator = "==" and left = right and outcome = true
  or
  operator = "==" and left != right and outcome = false
  or
  operator = "!=" and left != right and outcome = true
  or
  operator = "!=" and left = right and outcome = false
}

bindingset[left, operator, right]
private predicate compareStrings(string left, string operator, string right, boolean outcome) {
  operator = "==" and left.toLowerCase() = right.toLowerCase() and outcome = true
  or
  operator = "==" and left.toLowerCase() != right.toLowerCase() and outcome = false
  or
  operator = "!=" and left.toLowerCase() != right.toLowerCase() and outcome = true
  or
  operator = "!=" and left.toLowerCase() = right.toLowerCase() and outcome = false
}

bindingset[left, operator, right]
private predicate compareNumbers(float left, string operator, float right, boolean outcome) {
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

private predicate evaluateEquality(
  BinaryExpression expression, Event event, TStatusMode statusMode, boolean outcome
) {
  exists(string left, string right |
    getStringValue(expression.getLeftOperand(), event, left) and
    getStringValue(expression.getRightOperand(), event, right) and
    compareStrings(left, expression.getOperator(), right, outcome)
  )
  or
  exists(boolean left, boolean right |
    getBooleanValue(expression.getLeftOperand(), event, statusMode, left) and
    getBooleanValue(expression.getRightOperand(), event, statusMode, right) and
    compareBooleans(left, expression.getOperator(), right, outcome)
  )
  or
  exists(float left, float right |
    getNumberValue(expression.getLeftOperand(), left) and
    getNumberValue(expression.getRightOperand(), right) and
    compareNumbers(left, expression.getOperator(), right, outcome)
  )
  or
  isKnownNullValue(expression.getLeftOperand(), event) and
  isKnownNullValue(expression.getRightOperand(), event) and
  expression.getOperator() = "==" and
  outcome = true
  or
  isKnownNullValue(expression.getLeftOperand(), event) and
  isKnownNullValue(expression.getRightOperand(), event) and
  expression.getOperator() = "!=" and
  outcome = false
}

private predicate evaluateLogical(
  BinaryExpression expression, Event event, TStatusMode statusMode, boolean outcome
) {
  expression.getOperator() = "&&" and
  outcome = false and
  evaluatesToBooleanWithStatus([expression.getLeftOperand(), expression.getRightOperand()], event,
    statusMode, false)
  or
  expression.getOperator() = "&&" and
  outcome = true and
  evaluatesToBooleanWithStatus(expression.getLeftOperand(), event, statusMode, true) and
  evaluatesToBooleanWithStatus(expression.getRightOperand(), event, statusMode, true)
  or
  expression.getOperator() = "||" and
  outcome = true and
  evaluatesToBooleanWithStatus([expression.getLeftOperand(), expression.getRightOperand()], event,
    statusMode, true)
  or
  expression.getOperator() = "||" and
  outcome = false and
  evaluatesToBooleanWithStatus(expression.getLeftOperand(), event, statusMode, false) and
  evaluatesToBooleanWithStatus(expression.getRightOperand(), event, statusMode, false)
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
  getBooleanValue(node, event, statusMode, outcome)
  or
  isKnownNullValue(node, event) and outcome = false
  or
  exists(string value | getStringValue(node, event, value) |
    value = "" and outcome = false
    or
    value != "" and outcome = true
  )
  or
  exists(float value | getNumberValue(node, value) |
    value = 0 and outcome = false
    or
    value != 0 and outcome = true
  )
}

/** Holds if `node` may evaluate to `result` for `event`. */
predicate mayEvaluateToBoolean(ExpressionNode node, Event event, boolean outcome) {
  mayEvaluateToBooleanWithStatus(node, event, unknownStatusMode(), outcome)
}

private predicate mayEvaluateToBooleanWithStatus(
  ExpressionNode node, Event event, TStatusMode statusMode, boolean outcome
) {
  evaluatesToBooleanWithStatus(node, event, statusMode, outcome)
  or
  outcome in [false, true] and
  not exists(boolean known | evaluatesToBooleanWithStatus(node, event, statusMode, known))
}

/** Holds if the condition may permit execution for `event`. */
predicate isConditionFeasible(If condition, Event event) {
  mayEvaluateToBoolean(condition.getConditionExpr().getRoot(), event, true)
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
  mayEvaluateToBooleanAfterNeedsStatus(condition.getConditionExpr().getRoot(), event, status, true)
}

/** Holds if the condition contains a status-check function. */
predicate hasStatusCheckFunction(If condition) {
  exists(FunctionCallExpression call |
    call.getExpression() = condition.getConditionExpr() and
    call.getCallee().getName().toLowerCase() = ["always", "cancelled", "failure", "success"]
  )
}
