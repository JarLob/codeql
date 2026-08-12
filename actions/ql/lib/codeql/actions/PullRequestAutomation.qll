import codeql.actions.Ast
import codeql.actions.IntegratedExpressionControlFlow as IntegratedCfg
import codeql.actions.WorkflowRunSourceEvaluation as ExecutionContexts

bindingset[producer]
pragma[inline_late]
private predicate isAppTokenProducer(UsesStep producer) {
  producer.getCallee().toLowerCase() = "actions/create-github-app-token"
  or
  producer.getCallee().toLowerCase().matches("%/create-github-app-token")
}

bindingset[expression]
pragma[inline_late]
private UsesStep getAppTokenProducer(Expression expression) {
  exists(StepsExpression access, UsesStep producer |
    expression = access and
    access.getTarget() = producer and
    access.getFieldName().toLowerCase() = ["token", "github_token"] and
    isAppTokenProducer(producer) and
    result = producer
  )
}

bindingset[expression]
pragma[inline_late]
private predicate isWorkflowTriggeringCredential(Expression expression) {
  exists(getAppTokenProducer(expression))
}

bindingset[expression]
pragma[inline_late]
private string getWorkflowTriggeringActor(Expression expression) {
  exists(UsesStep producer, string app |
    producer = getAppTokenProducer(expression) and
    app = producer.getArgument(["github_app", "app-slug"]).trim().toLowerCase() and
    app != "" and
    (
      app.matches("%[bot]") and result = app
      or
      not app.matches("%[bot]") and result = app + "[bot]"
    )
  )
}

/** A step that updates a checked-out submodule from its configured remote. */
class RemoteSubmoduleUpdateStep extends Run {
  RemoteSubmoduleUpdateStep() {
    this.getScript()
        .getACommand()
        .toLowerCase()
        .regexpMatch(".*\\bgit\\s+submodule\\s+update\\b.*--remote(\\s|$).*")
  }
}

bindingset[creator]
pragma[inline_late]
private predicate remoteSubmoduleUpdatePrecedes(UsesStep creator) {
  exists(RemoteSubmoduleUpdateStep update, Event event |
    update.getEnclosingJob() = creator.getEnclosingJob() and
    event = creator.getATriggerEvent() and
    IntegratedCfg::orderedStepsMayReachForEvent(update, creator, event)
  )
}

/**
 * A `peter-evans/create-pull-request` invocation that can create a branch in the current
 * repository containing content imported from a remote submodule.
 */
class ExternallyInfluencedLocalPullRequestStep extends UsesStep {
  ExternallyInfluencedLocalPullRequestStep() {
    this.getCallee().toLowerCase() = "peter-evans/create-pull-request" and
    (
      not exists(this.getArgument("push-to-fork"))
      or
      this.getArgument("push-to-fork").trim() = ""
    ) and
    isWorkflowTriggeringCredential(this.getArgumentExpr("token")) and
    remoteSubmoduleUpdatePrecedes(this)
  }

  /** Gets a statically configured label applied when the pull request is created. */
  string getAnInitialLabel() {
    exists(string line |
      line = this.getArgument("labels").splitAt("\n").trim() and
      line != "" and
      result = line.splitAt(",").trim() and
      result != ""
    )
  }

  /** Gets the statically resolved App identity that creates the pull request. */
  string getCreatorLogin() { result = getWorkflowTriggeringActor(this.getArgumentExpr("token")) }
}

bindingset[command]
pragma[inline_late]
private string getAddedLabelFromGhCommand(string command) {
  result =
    command.regexpCapture(".*\\bgh\\s+pr\\s+edit\\b.*--add-label\\s+[\"']?([A-Za-z0-9_.:/-]+).*", 1)
}

/** A `gh pr edit --add-label` step authenticated with a modeled App token. */
class WorkflowTriggeringPullRequestLabelStep extends Run {
  WorkflowTriggeringPullRequestLabelStep() {
    exists(getAddedLabelFromGhCommand(this.getScript().getACommand())) and
    isWorkflowTriggeringCredential(this.getEnv().getEnvVarExpr(["GH_TOKEN", "GITHUB_TOKEN"]))
  }

  /** Gets a statically resolved label added by this step. */
  string getAddedLabel() { result = getAddedLabelFromGhCommand(this.getScript().getACommand()) }

  /** Gets the statically resolved App identity that adds the label. */
  string getTriggeringActorLogin() {
    result = getWorkflowTriggeringActor(this.getEnv().getEnvVarExpr(["GH_TOKEN", "GITHUB_TOKEN"]))
  }
}

bindingset[event]
pragma[inline_late]
private predicate pullRequestWorkflowMayExecuteSubmoduleContent(Event event) {
  event.getName() = "pull_request" and
  event.acceptsActivityType("opened") and
  exists(UsesStep checkout, Run execution |
    checkout.getATriggerEvent() = event and
    checkout.getCallee().toLowerCase() = "actions/checkout" and
    checkout.getArgument("submodules").trim().toLowerCase() = ["true", "recursive"] and
    execution.getATriggerEvent() = event and
    IntegratedCfg::orderedStepsMayReachForEvent(checkout, execution, event)
  )
}

bindingset[node]
pragma[inline_late]
private predicate expressionMatchesPullRequestLabel(ExpressionNode node, string label) {
  exists(FunctionCallExpression call |
    node = call and
    call.getCallee().getName().toLowerCase() = "contains" and
    call.getArgument(0) instanceof AccessExpression and
    call.getArgument(0).(AccessExpression).getAccessPath().toLowerCase() =
      "github.event.pull_request.labels.*.name" and
    call.getArgument(1) instanceof LiteralExpression and
    call.getArgument(1).(LiteralExpression).getKind() = "StringLiteral" and
    label =
      call.getArgument(1)
          .(LiteralExpression)
          .getValue()
          .substring(1, call.getArgument(1).(LiteralExpression).getValue().length() - 1)
          .regexpReplaceAll("''", "'")
  )
  or
  exists(BinaryExpression comparison, ExpressionNode access, LiteralExpression literal |
    node = comparison and
    comparison.getOperator() = "==" and
    access = [comparison.getLeftOperand(), comparison.getRightOperand()] and
    access instanceof AccessExpression and
    access.(AccessExpression).getAccessPath().toLowerCase() = "github.event.label.name" and
    literal = [comparison.getLeftOperand(), comparison.getRightOperand()] and
    literal != access and
    literal.getKind() = "StringLiteral" and
    label =
      literal.getValue().substring(1, literal.getValue().length() - 1).regexpReplaceAll("''", "'")
  )
}

bindingset[node]
pragma[inline_late]
private string getStringLiteralValue(ExpressionNode node) {
  node instanceof LiteralExpression and
  node.(LiteralExpression).getKind() = "StringLiteral" and
  result =
    node.(LiteralExpression)
        .getValue()
        .substring(1, node.(LiteralExpression).getValue().length() - 1)
        .regexpReplaceAll("''", "'")
}

private predicate expressionMatchesEventActor(ExpressionNode node, string actor) {
  exists(BinaryExpression comparison, ExpressionNode access, ExpressionNode literal |
    node = comparison and
    comparison.getOperator() = "==" and
    access = [comparison.getLeftOperand(), comparison.getRightOperand()] and
    getAccessPath(access) = "github.actor" and
    literal = [comparison.getLeftOperand(), comparison.getRightOperand()] and
    literal != access and
    actor = getStringLiteralValue(literal)
  )
}

private predicate expressionMatchesPullRequestAuthor(ExpressionNode node, string author) {
  exists(BinaryExpression comparison, ExpressionNode access, ExpressionNode literal |
    node = comparison and
    comparison.getOperator() = "==" and
    access = [comparison.getLeftOperand(), comparison.getRightOperand()] and
    getAccessPath(access) = "github.event.pull_request.user.login" and
    literal = [comparison.getLeftOperand(), comparison.getRightOperand()] and
    literal != access and
    author = getStringLiteralValue(literal)
  )
}

private predicate expressionMatchesPullRequestAutomationControl(
  ExpressionNode node, string kind, string value
) {
  kind = "label" and expressionMatchesPullRequestLabel(node, value)
  or
  kind = "event-actor" and expressionMatchesEventActor(node, value)
  or
  kind = "pull-request-author" and expressionMatchesPullRequestAuthor(node, value)
}

private predicate expressionTrueRequiresPullRequestAutomationControl(
  ExpressionNode node, string kind, string value
) {
  expressionMatchesPullRequestAutomationControl(node, kind, value)
  or
  node instanceof ExpressionRoot and
  expressionTrueRequiresPullRequestAutomationControl(node.getChild(0), kind, value)
  or
  node instanceof BinaryExpression and
  node.(BinaryExpression).getOperator() = "&&" and
  expressionTrueRequiresPullRequestAutomationControl([
      node.(BinaryExpression).getLeftOperand(), node.(BinaryExpression).getRightOperand()
    ], kind, value)
  or
  node instanceof BinaryExpression and
  node.(BinaryExpression).getOperator() = "||" and
  expressionTrueRequiresPullRequestAutomationControl(node.(BinaryExpression).getLeftOperand(), kind,
    value) and
  expressionTrueRequiresPullRequestAutomationControl(node.(BinaryExpression).getRightOperand(),
    kind, value)
}

bindingset[node]
pragma[inline_late]
private string getAccessPath(ExpressionNode node) {
  node instanceof AccessExpression and
  result = node.(AccessExpression).getAccessPath().toLowerCase()
}

private predicate expressionMatchesSameRepositoryPullRequestHead(ExpressionNode node) {
  exists(BinaryExpression comparison, ExpressionNode left, ExpressionNode right |
    node = comparison and
    comparison.getOperator() = "==" and
    left = comparison.getLeftOperand() and
    right = comparison.getRightOperand() and
    (
      getAccessPath(left) = "github.event.pull_request.head.repo.id" and
      getAccessPath(right) = "github.repository_id"
      or
      getAccessPath(right) = "github.event.pull_request.head.repo.id" and
      getAccessPath(left) = "github.repository_id"
      or
      getAccessPath(left) = "github.event.pull_request.head.repo.full_name" and
      getAccessPath(right) = "github.repository"
      or
      getAccessPath(right) = "github.event.pull_request.head.repo.full_name" and
      getAccessPath(left) = "github.repository"
    )
  )
}

private predicate expressionTrueRequiresSameRepositoryPullRequestHead(ExpressionNode node) {
  expressionMatchesSameRepositoryPullRequestHead(node)
  or
  node instanceof ExpressionRoot and
  expressionTrueRequiresSameRepositoryPullRequestHead(node.getChild(0))
  or
  node instanceof BinaryExpression and
  node.(BinaryExpression).getOperator() = "&&" and
  expressionTrueRequiresSameRepositoryPullRequestHead([
      node.(BinaryExpression).getLeftOperand(), node.(BinaryExpression).getRightOperand()
    ])
  or
  node instanceof BinaryExpression and
  node.(BinaryExpression).getOperator() = "||" and
  expressionTrueRequiresSameRepositoryPullRequestHead(node.(BinaryExpression).getLeftOperand()) and
  expressionTrueRequiresSameRepositoryPullRequestHead(node.(BinaryExpression).getRightOperand())
}

/** Holds if `condition` can only be true when `label` is present on the pull request. */
bindingset[condition]
pragma[inline_late]
predicate conditionRequiresPullRequestLabel(If condition, string label) {
  conditionRequiresPullRequestAutomationControl(condition, "label", label)
}

/** Gets an exact automation-satisfiable control required for `condition` to be true. */
bindingset[condition]
pragma[inline_late]
predicate conditionRequiresPullRequestAutomationControl(If condition, string kind, string value) {
  expressionTrueRequiresPullRequestAutomationControl(condition.getConditionExpr().getRoot(), kind,
    value)
}

/** Holds if `condition` can only be true for a same-repository pull request head. */
bindingset[condition]
pragma[inline_late]
predicate conditionRequiresSameRepositoryPullRequestHead(If condition) {
  expressionTrueRequiresSameRepositoryPullRequestHead(condition.getConditionExpr().getRoot())
}

private predicate expressionUsesStepOutput(Expression expression, Run producer) {
  exists(StepsExpression access |
    access = expression.getAChildNode*() and
    access.getTarget() = producer and
    producer.getScript().getAWriteToGitHubOutput(access.getFieldName(), _)
  )
  or
  exists(NeedsExpression access, Outputs outputs, Expression output |
    access = expression.getAChildNode*() and
    outputs = access.getTarget() and
    output = outputs.getOutputExpr(access.getFieldName()) and
    expressionUsesStepOutput(output, producer)
  )
}

bindingset[creator, labeler]
pragma[inline_late]
private predicate labelerSelectsCreatedPullRequest(
  ExternallyInfluencedLocalPullRequestStep creator, WorkflowTriggeringPullRequestLabelStep labeler
) {
  exists(string initialLabel, Run selection, Expression prNumber |
    initialLabel = creator.getAnInitialLabel() and
    selection.getEnclosingWorkflow() = labeler.getEnclosingWorkflow() and
    selection.getScript().getRawScript().indexOf(initialLabel) >= 0 and
    prNumber = labeler.getEnv().getEnvVarExpr("PR_NUMBER") and
    expressionUsesStepOutput(prNumber, selection)
  )
}

private string getSatisfiedPullRequestControl(
  ExternallyInfluencedLocalPullRequestStep creator, WorkflowTriggeringPullRequestLabelStep labeler,
  string kind
) {
  kind = "label" and result = labeler.getAddedLabel().toLowerCase()
  or
  kind = "event-actor" and result = labeler.getTriggeringActorLogin()
  or
  kind = "pull-request-author" and result = creator.getCreatorLogin()
}

/**
 * Gets a pull request event whose run may influence an App-token label mutation that can trigger
 * `targetEvent` for `label` on an automated same-repository pull request.
 */
bindingset[targetEvent]
pragma[inline_late]
Event getAnAutomatedLocalPullRequestControlSource(Event targetEvent, string kind, string value) {
  targetEvent.getName() = "pull_request" and
  targetEvent.acceptsActivityType("labeled") and
  exists(
    ExternallyInfluencedLocalPullRequestStep creator,
    WorkflowTriggeringPullRequestLabelStep labeler, Event workflowRunEvent
  |
    result.getName() = "pull_request" and
    pullRequestWorkflowMayExecuteSubmoduleContent(result) and
    result.getEnclosingWorkflow() != targetEvent.getEnclosingWorkflow() and
    creator.getEnclosingWorkflow().isInSameRepositoryAs(result.getEnclosingWorkflow()) and
    labeler.getEnclosingWorkflow().isInSameRepositoryAs(targetEvent.getEnclosingWorkflow()) and
    workflowRunEvent = labeler.getATriggerEvent() and
    workflowRunEvent.getName() = "workflow_run" and
    workflowRunEvent.acceptsWorkflowRunSourceEvent(result) and
    ExecutionContexts::mayExecuteForSource(labeler, workflowRunEvent, result) and
    labelerSelectsCreatedPullRequest(creator, labeler) and
    value = getSatisfiedPullRequestControl(creator, labeler, kind)
  )
}

/** Gets a source event that can automatically add `label` to an influenced local pull request. */
bindingset[targetEvent]
pragma[inline_late]
Event getAnAutomatedLocalPullRequestLabelSource(Event targetEvent, string label) {
  result = getAnAutomatedLocalPullRequestControlSource(targetEvent, "label", label)
}
