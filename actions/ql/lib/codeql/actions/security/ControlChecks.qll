import actions
private import codeql.actions.IntegratedExpressionBasicBlocks as IntegratedBlocks
private import codeql.actions.JobSynchronization as JobSync

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
      // actor and attacker have to be the same
      "pull_request_target",
      "workflow_run",
      "discussion_comment",
      "discussion",
      "issues",
      "fork",
      "watch"
    ]
}

string actor_not_attacker_event() {
  result =
    [
      // actor and attacker can be different
      // actor may be a collaborator, but the attacker is may be the author of the PR that gets commented
      // therefore it may be vulnerable to TOCTOU races where the actor reviews one thing and the attacker changes it
      "issue_comment",
      "pull_request_comment",
    ]
}

/**
 * Gets the outer caller of `ej`, i.e. the `ExternalJob` that calls the
 * reusable workflow containing `ej`. Used with transitive closure to
 * walk up nested reusable workflow chains.
 */
private ExternalJob getAnOuterCaller(ExternalJob ej) {
  result = ej.getEnclosingWorkflow().(ReusableWorkflow).getACaller()
}

/** An If node that contains an actor, user or label check */
abstract class ControlCheck extends AstNode {
  ControlCheck() {
    this instanceof If or
    this instanceof Environment or
    this instanceof UsesStep or
    this instanceof Run
  }

  private Job getProtectedJob(AstNode node) {
    node instanceof Job and result = node
    or
    not node instanceof Job and result = node.getEnclosingJob()
  }

  private predicate dominatesThroughSuccessfulNeededJob(AstNode node, Event event) {
    exists(Job checkedJob, Job protectedJob |
      checkedJob = this.getEnclosingJob() and
      protectedJob = this.getProtectedJob(node) and
      checkedJob != protectedJob and
      JobSync::jobExecutionRequiresSuccessfulCompletionOf(protectedJob, checkedJob, event) and
      (
        this instanceof If and checkedJob.getIf() = this
        or
        this instanceof Environment and checkedJob.getEnvironment() = this
        or
        (this instanceof Run or this instanceof UsesStep) and
        checkedJob instanceof LocalJob and
        checkedJob.(LocalJob).getAContainedStep() = this and
        not exists(this.(Step).getIf())
      )
    )
  }

  predicate protects(AstNode node, Event event, string category) {
    // The check dominates the step it should protect
    this.dominates(node, event) and
    // The check is effective against the event and category
    this.protectsCategoryAndEvent(category, event.getName()) and
    // The check can be triggered by the event
    this.getATriggerEvent() = event and
    // For reusable workflows, there must be no unprotected caller chain for this event.
    (
      not node.getEnclosingWorkflow() instanceof ReusableWorkflow
      or
      this.dominatesSameWorkflow(node, event)
      or
      not exists(ExternalJob directCaller |
        directCaller = node.getEnclosingWorkflow().(ReusableWorkflow).getACaller() and
        unprotectedCallerChain(directCaller, event, category)
      )
    )
  }

  /**
   * Holds if this control check must execute and pass before `node` can run.
   */
  predicate dominates(AstNode node, Event event) {
    this.dominatesSameWorkflow(node, event)
    or
    // When the node is inside a reusable workflow,
    // this check dominates via at least one caller chain.
    this.dominatesViaCaller(node, event, _)
  }

  /**
   * Holds if this control check dominates `node` within the same workflow.
   */
  predicate dominatesSameWorkflow(AstNode node, Event event) {
    this.getATriggerEvent() = event and
    (
      // Step-level: the check is an `if:` on the step containing `node`,
      // or on the enclosing job, or on a needed job/step.
      this instanceof If and
      (
        node.getEnclosingStep().getIf() = this or
        node.getEnclosingJob().getIf() = this or
        IntegratedBlocks::conditionTrueDominates(this, node) or
        this.dominatesThroughSuccessfulNeededJob(node, event)
      )
      or
      // Job-level: the check is an environment on the enclosing job or a needed job.
      this instanceof Environment and
      (
        node.getEnclosingJob().getEnvironment() = this or
        this.dominatesThroughSuccessfulNeededJob(node, event)
      )
      or
      // Step-level: the check is a Run/UsesStep that precedes `node`'s step
      // in the same job, or is a step in a needed job.
      (
        this instanceof Run or
        this instanceof UsesStep
      ) and
      (
        IntegratedBlocks::astNodeDominates(this, node) or
        this.dominatesThroughSuccessfulNeededJob(node, event)
      )
    )
  }

  /**
   * Holds if this control check dominates `node` in a reusable workflow
   * via the caller chain starting at `directCaller`.
   */
  predicate dominatesViaCaller(AstNode node, Event event, ExternalJob directCaller) {
    directCaller = node.getEnclosingWorkflow().(ReusableWorkflow).getACaller() and
    directCaller.getATriggerEvent() = event and
    exists(ExternalJob caller |
      caller = getAnOuterCaller*(directCaller) and
      this.dominatesCaller(caller)
    )
  }

  /**
   * Holds if this control check directly dominates `caller`.
   */
  predicate dominatesCaller(ExternalJob caller) {
    this instanceof If and
    (
      caller.getIf() = this or
      this.dominatesThroughSuccessfulNeededJob(caller, caller.getATriggerEvent())
    )
    or
    this instanceof Environment and
    (
      caller.getEnvironment() = this or
      this.dominatesThroughSuccessfulNeededJob(caller, caller.getATriggerEvent())
    )
    or
    (this instanceof Run or this instanceof UsesStep) and
    this.dominatesThroughSuccessfulNeededJob(caller, caller.getATriggerEvent())
  }

  abstract predicate protectsCategoryAndEvent(string category, string event);
}

/**
 * Holds if this control check directly protects `caller`.
 */
bindingset[caller, event, category]
private predicate protectedCaller(ExternalJob caller, Event event, string category) {
  exists(ControlCheck check |
    check.protectsCategoryAndEvent(category, event.getName()) and
    check.getATriggerEvent() = event and
    check.dominatesCaller(caller)
  )
}

cached
private newtype TCallerState =
  MkCallerState(ExternalJob caller, Event event, string category) {
    caller.getATriggerEvent() = event and
    category = any_category()
  }

private class CallerState extends TCallerState, MkCallerState {
  ExternalJob caller;
  Event event;
  string category;

  CallerState() { this = MkCallerState(caller, event, category) }

  ExternalJob getCaller() { result = caller }

  Event getEvent() { result = event }

  string getCategory() { result = category }

  /**
   * Gets an outer caller state if this caller is not protected.
   */
  CallerState getUnprotectedOuterState() {
    not protectedCaller(this.getCaller(), this.getEvent(), this.getCategory()) and
    result = MkCallerState(getAnOuterCaller(this.getCaller()), this.getEvent(), this.getCategory())
  }

  predicate isUnprotectedOutermost() {
    not protectedCaller(this.getCaller(), this.getEvent(), this.getCategory()) and
    not exists(getAnOuterCaller(this.getCaller()))
  }

  string toString() { result = caller + " / " + event + " / " + category }
}

/**
 * Holds if there is a caller path from `caller` to an outer workflow that has no protection.
 */
bindingset[caller, event, category]
private predicate unprotectedCallerChain(ExternalJob caller, Event event, string category) {
  exists(CallerState start, CallerState outermost |
    start = MkCallerState(caller, event, category) and
    outermost = start.getUnprotectedOuterState*() and
    outermost.isUnprotectedOutermost()
  )
}

abstract class AssociationCheck extends ControlCheck {
  // Checks if the actor is a MEMBER/OWNER the repo
  // - they are effective against pull requests and workflow_run (since these are triggered by pull_requests) since they can control who is making the PR
  // - they are not effective against issue_comment since the author of the comment may not be the same as the author of the PR
  override predicate protectsCategoryAndEvent(string category, string event) {
    event = actor_is_attacker_event() and category = any_category()
    or
    event = actor_not_attacker_event() and category = non_toctou_category()
  }
}

abstract class ActorCheck extends ControlCheck {
  // checks for a specific actor
  // - they are effective against pull requests and workflow_run (since these are triggered by pull_requests) since they can control who is making the PR
  // - they are not effective against issue_comment since the author of the comment may not be the same as the author of the PR
  override predicate protectsCategoryAndEvent(string category, string event) {
    event = actor_is_attacker_event() and category = any_category()
    or
    event = actor_not_attacker_event() and category = non_toctou_category()
  }
}

abstract class RepositoryCheck extends ControlCheck {
  // checks that the origin of the code is the same as the repository.
  // for pull_requests, that means that it triggers only on local branches or repos from the same org
  // - they are effective against pull requests/workflow_run since they can control where the code is coming from
  // - they are not effective against issue_comment since the repository will always be the same
}

abstract class PermissionCheck extends ControlCheck {
  // checks that the actor has a specific permission level
  // - they are effective against pull requests/workflow_run since they can control who can make changes
  // - they are not effective against issue_comment since the author of the comment may not be the same as the author of the PR
  override predicate protectsCategoryAndEvent(string category, string event) {
    event = actor_is_attacker_event() and category = any_category()
    or
    event = actor_not_attacker_event() and category = non_toctou_category()
  }
}

abstract class LabelCheck extends ControlCheck {
  // checks if the issue/pull_request is labeled, which implies that it could have been approved
  // - they dont protect against mutation attacks
  override predicate protectsCategoryAndEvent(string category, string event) {
    event = actor_is_attacker_event() and category = any_category()
    or
    event = actor_not_attacker_event() and category = non_toctou_category()
  }
}

class EnvironmentCheck extends ControlCheck instanceof Environment {
  // Environment checks are not effective against any mutable attacks
  // they do actually protect against untrusted code execution (sha)
  override predicate protectsCategoryAndEvent(string category, string event) {
    event = actor_is_attacker_event() and category = any_category()
    or
    event = actor_not_attacker_event() and category = non_toctou_category()
  }
}

abstract class CommentVsHeadDateCheck extends ControlCheck {
  override predicate protectsCategoryAndEvent(string category, string event) {
    // by itself, this check is not effective against any attacks
    event = actor_not_attacker_event() and category = toctou_category()
  }
}

/* Specific implementations of control checks */
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

private predicate parsedConditionProtectsCategoryAndEvent(
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

private predicate isParsedCheckOwner(If condition, string kind) {
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

class LabelIfCheck extends LabelCheck instanceof If {
  LabelIfCheck() { exists(this.getConditionExpr().getRoot()) and isParsedCheckOwner(this, "label") }

  override predicate protectsCategoryAndEvent(string category, string event) {
    exists(this.(If).getConditionExpr().getRoot()) and
    parsedConditionProtectsCategoryAndEvent(this.(If), category, event)
  }
}

class ActorIfCheck extends ActorCheck instanceof If {
  ActorIfCheck() { exists(this.getConditionExpr().getRoot()) and isParsedCheckOwner(this, "actor") }

  override predicate protectsCategoryAndEvent(string category, string event) {
    exists(this.(If).getConditionExpr().getRoot()) and
    parsedConditionProtectsCategoryAndEvent(this.(If), category, event)
  }
}

class PullRequestTargetRepositoryIfCheck extends RepositoryCheck instanceof If {
  PullRequestTargetRepositoryIfCheck() {
    exists(this.getConditionExpr().getRoot()) and
    isParsedCheckOwner(this, "pull-request-repository")
  }

  override predicate protectsCategoryAndEvent(string category, string event) {
    exists(this.(If).getConditionExpr().getRoot()) and
    parsedConditionProtectsCategoryAndEvent(this.(If), category, event)
  }
}

class WorkflowRunRepositoryIfCheck extends RepositoryCheck instanceof If {
  WorkflowRunRepositoryIfCheck() {
    exists(this.getConditionExpr().getRoot()) and
    isParsedCheckOwner(this, "workflow-run-repository")
  }

  override predicate protectsCategoryAndEvent(string category, string event) {
    exists(this.(If).getConditionExpr().getRoot()) and
    parsedConditionProtectsCategoryAndEvent(this.(If), category, event)
  }
}

class AssociationIfCheck extends AssociationCheck instanceof If {
  AssociationIfCheck() {
    exists(this.getConditionExpr().getRoot()) and isParsedCheckOwner(this, "association")
  }

  override predicate protectsCategoryAndEvent(string category, string event) {
    exists(this.(If).getConditionExpr().getRoot()) and
    parsedConditionProtectsCategoryAndEvent(this.(If), category, event)
  }
}

class AssociationActionCheck extends AssociationCheck instanceof UsesStep {
  AssociationActionCheck() {
    this.getCallee() = "TheModdingInquisition/actions-team-membership" and
    (
      not exists(this.getArgument("exit"))
      or
      this.getArgument("exit") = "true"
    )
    or
    this.getCallee() = "actions/github-script" and
    this.getArgument("script").splitAt("\n").matches("%getMembershipForUserInOrg%")
    or
    this.getCallee() = "octokit/request-action" and
    this.getArgument("route").regexpMatch("GET.*(memberships).*")
  }
}

class PermissionActionCheck extends PermissionCheck instanceof UsesStep {
  PermissionActionCheck() {
    this.getCallee() = "actions-cool/check-user-permission" and
    (
      // default permission level is write
      not exists(this.getArgument("permission-level")) or
      this.getArgument("require") = ["write", "admin"]
    )
    or
    this.getCallee() = "sushichop/action-repository-permission" and
    this.getArgument("required-permission") = ["write", "admin"]
    or
    this.getCallee() = "prince-chrismc/check-actor-permissions-action" and
    this.getArgument("permission") = ["write", "admin"]
    or
    this.getCallee() = "lannonbr/repo-permission-check-action" and
    this.getArgument("permission") = ["write", "admin"]
    or
    this.getCallee() = "xt0rted/slash-command-action" and
    (
      // default permission level is write
      not exists(this.getArgument("permission-level")) or
      this.getArgument("permission-level") = ["write", "admin"]
    )
    or
    this.getCallee() = "actions/github-script" and
    this.getArgument("script").splitAt("\n").matches("%getCollaboratorPermissionLevel%")
    or
    this.getCallee() = "octokit/request-action" and
    this.getArgument("route").regexpMatch("GET.*(collaborators|permission).*")
  }
}

class BashCommentVsHeadDateCheck extends CommentVsHeadDateCheck, Run {
  BashCommentVsHeadDateCheck() {
    // eg: if [[ $(date -d "$pushed_at" +%s) -gt $(date -d "$COMMENT_AT" +%s) ]]; then
    exists(string cmd1, string cmd2 |
      cmd1 = this.getScript().getACommand() and
      cmd2 = this.getScript().getACommand() and
      not cmd1 = cmd2 and
      cmd1.toLowerCase().regexpMatch("date\\s+-d.*(commit|pushed|comment|commented)_at.*") and
      cmd2.toLowerCase().regexpMatch("date\\s+-d.*(commit|pushed|comment|commented)_at.*")
    )
  }
}
