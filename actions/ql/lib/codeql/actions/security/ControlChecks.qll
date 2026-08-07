import actions
private import codeql.actions.IntegratedExpressionBasicBlocks as IntegratedBlocks
private import codeql.actions.JobSynchronization as JobSync
private import codeql.actions.config.Config
private import codeql.actions.security.ControlCheckConditions as Conditions

string any_category() { result = Conditions::any_category() }

string non_toctou_category() { result = Conditions::non_toctou_category() }

string toctou_category() { result = Conditions::toctou_category() }

string any_event() { result = Conditions::any_event() }

string actor_is_attacker_event() { result = Conditions::actor_is_attacker_event() }

string actor_not_attacker_event() { result = Conditions::actor_not_attacker_event() }

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

/** A recognized attempt to authorize access to untrusted code. */
abstract class AuthorizationAttemptCheck extends ControlCheck {
  private string getConditionKind() {
    this instanceof LabelIfCheck and result = "label"
    or
    this instanceof ActorIfCheck and result = "actor"
    or
    this instanceof AssociationIfCheck and result = "association"
    or
    this instanceof PullRequestTargetRepositoryIfCheck and result = "pull-request-repository"
    or
    this instanceof WorkflowRunRepositoryIfCheck and result = "workflow-run-repository"
  }

  /**
   * Holds if this attempt applies to `event`. A condition-based attempt applies only when its
   * recognized atom can be evaluated for the event.
   */
  predicate appliesToEvent(Event event) {
    not this instanceof If
    or
    Conditions::parsedCheckAppliesToEvent(this.(If), this.getConditionKind(), event)
  }

  /** Holds if this attempt applies to a concrete workflow-run source event. */
  bindingset[event, sourceEvent]
  pragma[inline_late]
  predicate appliesToWorkflowRunSource(Event event, Event sourceEvent) {
    not this instanceof If
    or
    Conditions::parsedCheckAppliesToWorkflowRunSource(this.(If), this.getConditionKind(), event,
      sourceEvent)
  }
}

abstract class AssociationCheck extends AuthorizationAttemptCheck {
  // Checks if the actor is a MEMBER/OWNER the repo
  // - they are effective against pull requests and workflow_run (since these are triggered by pull_requests) since they can control who is making the PR
  // - they are not effective against issue_comment since the author of the comment may not be the same as the author of the PR
  override predicate protectsCategoryAndEvent(string category, string event) {
    event = actor_is_attacker_event() and category = any_category()
    or
    event = actor_not_attacker_event() and category = non_toctou_category()
  }
}

abstract class ActorCheck extends AuthorizationAttemptCheck {
  // checks for a specific actor
  // - they are effective against pull requests and workflow_run (since these are triggered by pull_requests) since they can control who is making the PR
  // - they are not effective against issue_comment since the author of the comment may not be the same as the author of the PR
  override predicate protectsCategoryAndEvent(string category, string event) {
    event = actor_is_attacker_event() and category = any_category()
    or
    event = actor_not_attacker_event() and category = non_toctou_category()
  }
}

abstract class RepositoryCheck extends AuthorizationAttemptCheck {
  // checks that the origin of the code is the same as the repository.
  // for pull_requests, that means that it triggers only on local branches or repos from the same org
  // - they are effective against pull requests/workflow_run since they can control where the code is coming from
  // - they are not effective against issue_comment since the repository will always be the same
}

abstract class PermissionCheck extends AuthorizationAttemptCheck {
  // checks that the actor has a specific permission level
  // - they are effective against pull requests/workflow_run since they can control who can make changes
  // - they are not effective against issue_comment since the author of the comment may not be the same as the author of the PR
  override predicate protectsCategoryAndEvent(string category, string event) {
    event = actor_is_attacker_event() and category = any_category()
    or
    event = actor_not_attacker_event() and category = non_toctou_category()
  }
}

abstract class LabelCheck extends AuthorizationAttemptCheck {
  // checks if the issue/pull_request is labeled, which implies that it could have been approved
  // - they dont protect against mutation attacks
  override predicate protectsCategoryAndEvent(string category, string event) {
    event = any_event() and category = non_toctou_category()
  }
}

class EnvironmentCheck extends ControlCheck instanceof Environment {
  EnvironmentCheck() {
    this.getName().trim() != "" and
    environmentProtectionDataModel(this.getName(), "required-reviewer", true) and
    not environmentProtectionDataModel(this.getName(), "required-reviewer", false)
  }

  // Environment checks are not effective against any mutable attacks
  // they do actually protect against untrusted code execution (sha)
  override predicate protectsCategoryAndEvent(string category, string event) {
    event = any_event() and category = non_toctou_category()
  }
}

abstract class CommentVsHeadDateCheck extends ControlCheck {
  override predicate protectsCategoryAndEvent(string category, string event) {
    // by itself, this check is not effective against any attacks
    event = actor_not_attacker_event() and category = toctou_category()
  }
}

/* Specific implementations of control checks */
class LabelIfCheck extends LabelCheck instanceof If {
  LabelIfCheck() {
    exists(this.getConditionExpr().getRoot()) and Conditions::isParsedCheckOwner(this, "label")
  }

  override predicate protectsCategoryAndEvent(string category, string event) {
    exists(this.(If).getConditionExpr().getRoot()) and
    Conditions::parsedConditionProtectsCategoryAndEvent(this.(If), category, event)
  }
}

class ActorIfCheck extends ActorCheck instanceof If {
  ActorIfCheck() {
    exists(this.getConditionExpr().getRoot()) and Conditions::isParsedCheckOwner(this, "actor")
  }

  override predicate protectsCategoryAndEvent(string category, string event) {
    exists(this.(If).getConditionExpr().getRoot()) and
    Conditions::parsedConditionProtectsCategoryAndEvent(this.(If), category, event)
  }
}

class PullRequestTargetRepositoryIfCheck extends RepositoryCheck instanceof If {
  PullRequestTargetRepositoryIfCheck() {
    exists(this.getConditionExpr().getRoot()) and
    Conditions::isParsedCheckOwner(this, "pull-request-repository")
  }

  override predicate protectsCategoryAndEvent(string category, string event) {
    exists(this.(If).getConditionExpr().getRoot()) and
    Conditions::parsedConditionProtectsCategoryAndEvent(this.(If), category, event)
  }
}

class WorkflowRunRepositoryIfCheck extends RepositoryCheck instanceof If {
  WorkflowRunRepositoryIfCheck() {
    exists(this.getConditionExpr().getRoot()) and
    Conditions::isParsedCheckOwner(this, "workflow-run-repository")
  }

  override predicate protectsCategoryAndEvent(string category, string event) {
    exists(this.(If).getConditionExpr().getRoot()) and
    Conditions::parsedConditionProtectsCategoryAndEvent(this.(If), category, event)
  }
}

class AssociationIfCheck extends AssociationCheck instanceof If {
  AssociationIfCheck() {
    exists(this.getConditionExpr().getRoot()) and
    Conditions::isParsedCheckOwner(this, "association")
  }

  override predicate protectsCategoryAndEvent(string category, string event) {
    exists(this.(If).getConditionExpr().getRoot()) and
    Conditions::parsedConditionProtectsCategoryAndEvent(this.(If), category, event)
  }
}

class AssociationActionCheck extends AssociationCheck instanceof UsesStep {
  AssociationActionCheck() {
    this.getCallee() = "TheModdingInquisition/actions-team-membership" and
    failureStopsStep(this) and
    (
      not exists(this.getArgument("exit"))
      or
      this.getArgument("exit").trim().toLowerCase() = "true"
    )
    or
    this.getCallee() = "actions/github-script" and
    this.getArgument("script").splitAt("\n").matches("%getMembershipForUserInOrg%")
    or
    this.getCallee() = "octokit/request-action" and
    this.getArgument("route").regexpMatch("GET.*(memberships).*")
  }
}

private predicate failureStopsStep(Step step) {
  not exists(step.getContinueOnErrorValue())
  or
  step.getContinueOnErrorValue().trim().toLowerCase() = "false"
}

/** A membership check configured so that an authorization failure does not stop execution. */
class IneffectiveAssociationActionCheck extends AuthorizationAttemptCheck instanceof UsesStep {
  IneffectiveAssociationActionCheck() {
    this.getCallee() = "TheModdingInquisition/actions-team-membership" and
    not this instanceof AssociationActionCheck
  }

  override predicate protectsCategoryAndEvent(string category, string event) { none() }
}

private predicate isFalseStringLiteral(ExpressionNode node) {
  node instanceof LiteralExpression and
  node.(LiteralExpression).getKind() = "StringLiteral" and
  node.(LiteralExpression).getValue().toLowerCase() = ["'false'", "\"false\""]
}

private predicate checksActionsCoolRequireResult(If condition, UsesStep action) {
  exists(BinaryExpression comparison, AccessExpression output, LiteralExpression falseValue |
    comparison = condition.getConditionExpr().getRoot().getChild(0) and
    comparison.getOperator() = "==" and
    output.getAccessPath().toLowerCase() =
      ("steps." + action.getId() + ".outputs.require-result").toLowerCase() and
    (
      output = comparison.getLeftOperand() and
      falseValue = comparison.getRightOperand()
      or
      falseValue = comparison.getLeftOperand() and
      output = comparison.getRightOperand()
    ) and
    isFalseStringLiteral(falseValue)
  )
}

private predicate runExitsNonzero(Run run) {
  exists(string command |
    command = run.getScript().getACommand() and
    command.trim().regexpMatch("exit\\s+[1-9][0-9]*")
  )
}

private predicate hasActionsCoolFailureGate(UsesStep action) {
  exists(Run gate |
    action.getNextStep() = gate and
    checksActionsCoolRequireResult(gate.getIf(), action) and
    runExitsNonzero(gate) and
    failureStopsStep(gate)
  )
}

private predicate actionsCoolSupportsErrorIfMissing(UsesStep action) {
  actionsControlBehaviorDataModel(action.getCallee(), action.getVersion(), "error-if-missing")
}

private predicate isKnownPermissionActionAttempt(UsesStep action) {
  action.getCallee() = "actions-cool/check-user-permission" and
  exists(action.getArgument("require"))
  or
  action.getCallee() = "sushichop/action-repository-permission" and
  exists(action.getArgument("required-permission"))
  or
  action.getCallee() =
    ["prince-chrismc/check-actor-permissions-action", "lannonbr/repo-permission-check-action"] and
  exists(action.getArgument("permission"))
  or
  action.getCallee() = "xt0rted/slash-command-action" and
  exists(action.getArgument("permission-level"))
}

class PermissionActionCheck extends PermissionCheck instanceof UsesStep {
  PermissionActionCheck() {
    this.getCallee() = "actions-cool/check-user-permission" and
    this.getArgument("require") = ["write", "admin"] and
    failureStopsStep(this) and
    (
      actionsCoolSupportsErrorIfMissing(this) and
      this.getArgument("error-if-missing").trim().toLowerCase() = "true"
      or
      hasActionsCoolFailureGate(this)
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

/** A recognized permission check whose configured threshold or failure behavior is ineffective. */
class IneffectivePermissionActionCheck extends AuthorizationAttemptCheck instanceof UsesStep {
  IneffectivePermissionActionCheck() {
    isKnownPermissionActionAttempt(this) and
    not this instanceof PermissionActionCheck
  }

  override predicate protectsCategoryAndEvent(string category, string event) { none() }
}

bindingset[command]
pragma[inline_late]
private predicate isHeadPushDateCommand(string command) {
  command.toLowerCase().regexpMatch("date\\s+-d.*(commit|pushed)_at.*")
  or
  command.toLowerCase().regexpMatch("jq\\s+.*\\.head\\.repo\\.pushed_at.*fromdateiso8601.*")
}

bindingset[command]
pragma[inline_late]
private predicate isCommentDateCommand(string command) {
  command.toLowerCase().regexpMatch("date\\s+-d.*(comment(_created)?_at|commented_at).*")
  or
  command
      .toLowerCase()
      .regexpMatch("jq\\s+.*(comment(_created)?_at|comment\\.created_at|commented_at).*fromdateiso8601.*")
}

class BashCommentVsHeadDateCheck extends CommentVsHeadDateCheck, Run {
  BashCommentVsHeadDateCheck() {
    // eg: if [[ $(date -d "$pushed_at" +%s) -gt $(date -d "$COMMENT_AT" +%s) ]]; then
    exists(string headCommand, string commentCommand |
      headCommand = this.getScript().getACommand() and
      commentCommand = this.getScript().getACommand() and
      headCommand != commentCommand and
      isHeadPushDateCommand(headCommand) and
      isCommentDateCommand(commentCommand)
    )
  }
}
