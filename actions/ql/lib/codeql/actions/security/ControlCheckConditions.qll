import actions

string any_category() {
  result =
    [
      "untrusted-checkout", "output-clobbering", "envpath-injection", "envvar-injection",
      "command-injection", "argument-injection", "code-injection", "cache-poisoning",
      "untrusted-checkout-toctou", "artifact-poisoning", "artifact-poisoning-toctou"
    ]
}

string non_toctou_category() {
  result = any_category() and not result = "untrusted-checkout-toctou"
}

string toctou_category() { result = ["untrusted-checkout-toctou", "artifact-poisoning-toctou"] }

string any_event() { result = actor_not_attacker_event() or result = actor_is_attacker_event() }

string actor_is_attacker_event() {
  result =
    [
      "pull_request_target", "workflow_run", "discussion_comment", "discussion", "issues",
      "fork", "watch"
    ]
}

string actor_not_attacker_event() { result = ["issue_comment", "pull_request_comment"] }

private predicate accessesPath(ExpressionNode node, string path) {
  node instanceof AccessExpression and node.(AccessExpression).getAccessPath() = path
}

private predicate containsAccessPath(ExpressionNode node, string path) {
  accessesPath(node.getAChild*(), path)
}

private predicate isAtomicCheck(ExpressionNode node) {
  node instanceof BinaryExpression and
  node.(BinaryExpression).getOperator() != ["&&", "||"]
  or
  node instanceof FunctionCallExpression
}

private predicate isLabelCheckAtom(ExpressionNode node) {
  exists(FunctionCallExpression call |
    node = call and
    call.getCallee().getName().toLowerCase() = "contains" and
    accessesPath(call.getArgument(0), "github.event.pull_request.labels.*.name")
  )
  or
  exists(BinaryExpression comparison, ExpressionNode operand |
    node = comparison and
    comparison.getOperator() = "==" and
    operand = [comparison.getLeftOperand(), comparison.getRightOperand()] and
    accessesPath(operand, "github.event.label.name")
  )
}

private predicate containsBotLiteral(ExpressionNode node) {
  exists(LiteralExpression literal |
    literal = node.getAChild*() and
    literal.getKind() = "StringLiteral" and
    literal.getValue().toLowerCase().matches("%[bot]%")
  )
}

private predicate isActorCheckAtom(ExpressionNode node) {
  isAtomicCheck(node) and
  (
    containsAccessPath(node,
      [
        "github.event.pull_request.user.login", "github.event.head_commit.author.name",
        "github.event.commits.*.author.name", "github.event.sender.login"
      ])
    or
    containsAccessPath(node, ["github.actor", "github.triggering_actor"]) and
    not containsBotLiteral(node)
  )
}

private predicate isAssociationCheckAtom(ExpressionNode node) {
  isAtomicCheck(node) and
  containsAccessPath(node,
    [
      "github.event.comment.author_association", "github.event.issue.author_association",
      "github.event.pull_request.author_association"
    ])
}

private predicate isPullRequestRepositoryCheckAtom(ExpressionNode node) {
  isAtomicCheck(node) and
  containsAccessPath(node,
    [
      "github.repository", "github.repository_owner",
      "github.event.pull_request.head.repo.full_name",
      "github.event.pull_request.head.repo.owner.name",
      "github.event.workflow_run.head_repository.full_name",
      "github.event.workflow_run.head_repository.owner.name"
    ])
}

private predicate isWorkflowRunRepositoryCheckAtom(ExpressionNode node) {
  isAtomicCheck(node) and
  containsAccessPath(node,
    [
      "github.event.workflow_run.head_repository.full_name",
      "github.event.workflow_run.head_repository.owner.name"
    ])
}

private newtype TProtectionContext =
  MkProtectionContext(string category, string event) {
    category = any_category() and event = any_event()
  }

private class ProtectionContext extends TProtectionContext {
  string category;
  string event;

  ProtectionContext() { this = MkProtectionContext(category, event) }

  string getCategory() { result = category }

  string getEvent() { result = event }

  string toString() { result = category + "@" + event }
}

private predicate atomProtectsCategoryAndEvent(ExpressionNode node, ProtectionContext context) {
  (isLabelCheckAtom(node) or isActorCheckAtom(node) or isAssociationCheckAtom(node)) and
  (
    context.getEvent() = actor_is_attacker_event() and context.getCategory() = any_category()
    or
    context.getEvent() = actor_not_attacker_event() and
    context.getCategory() = non_toctou_category()
  )
  or
  isPullRequestRepositoryCheckAtom(node) and
  context.getEvent() = "pull_request_target" and
  context.getCategory() = any_category()
  or
  isWorkflowRunRepositoryCheckAtom(node) and
  context.getEvent() = "workflow_run" and
  context.getCategory() = any_category()
}

private predicate hasKnownLiteralTruthiness(ExpressionNode node, boolean outcome) {
  node instanceof LiteralExpression and
  (
    node.getKind() = "BooleanLiteral" and
    node.(LiteralExpression).getValue().toLowerCase() = outcome.toString()
    or
    node.getKind() = "NullLiteral" and outcome = false
    or
    node.getKind() = "StringLiteral" and
    (
      node.(LiteralExpression).getValue() = "''" and outcome = false
      or
      node.(LiteralExpression).getValue() != "''" and outcome = true
    )
    or
    node.getKind() = "NumberLiteral" and
    (
      node.(LiteralExpression).getValue().toFloat() = 0 and outcome = false
      or
      node.(LiteralExpression).getValue().toFloat() != 0 and outcome = true
    )
  )
}

private predicate expressionTrueIsProtected(ExpressionNode node, ProtectionContext context) {
  hasKnownLiteralTruthiness(node, false)
  or
  atomProtectsCategoryAndEvent(node, context)
  or
  node instanceof ExpressionRoot and
  expressionTrueIsProtected(node.getChild(0), context)
  or
  node instanceof UnaryExpression and
  expressionFalseIsProtected(node.(UnaryExpression).getOperand(), context)
  or
  node instanceof BinaryExpression and
  node.(BinaryExpression).getOperator() = "&&" and
  (
    expressionTrueIsProtected(node.(BinaryExpression).getLeftOperand(), context)
    or
    expressionTrueIsProtected(node.(BinaryExpression).getRightOperand(), context)
  )
  or
  node instanceof BinaryExpression and
  node.(BinaryExpression).getOperator() = "||" and
  expressionTrueIsProtected(node.(BinaryExpression).getLeftOperand(), context) and
  (
    expressionFalseIsProtected(node.(BinaryExpression).getLeftOperand(), context)
    or
    expressionTrueIsProtected(node.(BinaryExpression).getRightOperand(), context)
  )
}

private predicate expressionFalseIsProtected(ExpressionNode node, ProtectionContext context) {
  hasKnownLiteralTruthiness(node, true)
  or
  node instanceof ExpressionRoot and
  expressionFalseIsProtected(node.getChild(0), context)
  or
  node instanceof UnaryExpression and
  expressionTrueIsProtected(node.(UnaryExpression).getOperand(), context)
  or
  node instanceof BinaryExpression and
  node.(BinaryExpression).getOperator() = "&&" and
  expressionFalseIsProtected(node.(BinaryExpression).getLeftOperand(), context) and
  (
    expressionTrueIsProtected(node.(BinaryExpression).getLeftOperand(), context)
    or
    expressionFalseIsProtected(node.(BinaryExpression).getRightOperand(), context)
  )
  or
  node instanceof BinaryExpression and
  node.(BinaryExpression).getOperator() = "||" and
  (
    expressionFalseIsProtected(node.(BinaryExpression).getLeftOperand(), context)
    or
    expressionFalseIsProtected(node.(BinaryExpression).getRightOperand(), context)
  )
}

predicate parsedConditionProtectsCategoryAndEvent(
  If condition, string category, string event
) {
  exists(ProtectionContext context, ExpressionRoot root |
    context.getCategory() = category and
    context.getEvent() = event and
    condition.getATriggerEvent().getName() = event and
    root = condition.getConditionExpr().getRoot() and
    expressionTrueIsProtected(root, context)
  )
}

private predicate expressionTrueCanReachConditionTrue(ExpressionNode node) {
  node instanceof ExpressionRoot
  or
  exists(ExpressionNode parent |
    parent = node.getParent() and
    (
      parent instanceof ExpressionRoot and expressionTrueCanReachConditionTrue(parent)
      or
      parent instanceof UnaryExpression and expressionFalseCanReachConditionTrue(parent)
      or
      parent instanceof BinaryExpression and
      parent.(BinaryExpression).getOperator() = "&&" and
      (
        node = parent.(BinaryExpression).getLeftOperand() and
        (
          expressionTrueCanReachConditionTrue(parent)
          or
          expressionFalseCanReachConditionTrue(parent)
        )
        or
        node = parent.(BinaryExpression).getRightOperand() and
        expressionTrueCanReachConditionTrue(parent)
      )
      or
      parent instanceof BinaryExpression and
      parent.(BinaryExpression).getOperator() = "||" and
      expressionTrueCanReachConditionTrue(parent)
    )
  )
}

private predicate expressionFalseCanReachConditionTrue(ExpressionNode node) {
  exists(ExpressionNode parent |
    parent = node.getParent() and
    (
      parent instanceof UnaryExpression and expressionTrueCanReachConditionTrue(parent)
      or
      parent instanceof BinaryExpression and
      parent.(BinaryExpression).getOperator() = "&&" and
      expressionFalseCanReachConditionTrue(parent)
      or
      parent instanceof BinaryExpression and
      parent.(BinaryExpression).getOperator() = "||" and
      (
        node = parent.(BinaryExpression).getLeftOperand() and
        (
          expressionTrueCanReachConditionTrue(parent)
          or
          expressionFalseCanReachConditionTrue(parent)
        )
        or
        node = parent.(BinaryExpression).getRightOperand() and
        expressionFalseCanReachConditionTrue(parent)
      )
    )
  )
}

predicate isParsedCheckOwner(If condition, string kind) {
  exists(ExpressionNode atom |
    atom.getExpression() = condition.getConditionExpr() and
    (
      kind = "label" and isLabelCheckAtom(atom)
      or
      kind = "actor" and isActorCheckAtom(atom)
      or
      kind = "association" and isAssociationCheckAtom(atom)
      or
      kind = "pull-request-repository" and isPullRequestRepositoryCheckAtom(atom)
      or
      kind = "workflow-run-repository" and isWorkflowRunRepositoryCheckAtom(atom)
    ) and
    expressionTrueCanReachConditionTrue(atom)
  )
}

private predicate isTrustedAssociationLiteral(ExpressionNode node) {
  node instanceof LiteralExpression and
  node.(LiteralExpression).getKind() = "StringLiteral" and
  node.(LiteralExpression).getValue().toUpperCase() =
    ["'MEMBER'", "\"MEMBER\"", "'OWNER'", "\"OWNER\""]
}

private predicate isAuthorAssociationAccess(ExpressionNode node) {
  node instanceof AccessExpression and
  node.(AccessExpression).getAccessPath() =
    [
      "github.event.comment.author_association", "github.event.issue.author_association",
      "github.event.pull_request.author_association"
    ]
}

predicate conditionRequiresTrustedAssociation(If condition) {
  exists(BinaryExpression comparison |
    comparison = condition.getConditionExpr().getRoot().getChild(0) and
    comparison.getOperator() = "==" and
    (
      isAuthorAssociationAccess(comparison.getLeftOperand()) and
      isTrustedAssociationLiteral(comparison.getRightOperand())
      or
      isTrustedAssociationLiteral(comparison.getLeftOperand()) and
      isAuthorAssociationAccess(comparison.getRightOperand())
    )
  )
}