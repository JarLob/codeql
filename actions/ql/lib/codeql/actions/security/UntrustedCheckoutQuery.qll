import actions
private import codeql.actions.DataFlow
private import codeql.actions.config.Config
private import codeql.actions.dataflow.FlowSources
private import codeql.actions.TaintTracking
private import codeql.actions.security.ControlChecks
private import codeql.actions.security.ControlCheckConditions as Conditions
private import codeql.actions.security.PoisonableSteps
private import codeql.actions.IntegratedExpressionControlFlow as IntegratedCfg
private import codeql.actions.JobSynchronization as JobSync

string checkoutTriggers() {
  result = ["pull_request_target", "workflow_run", "workflow_call", "issue_comment"]
}

private predicate hasUnsafePrCheckoutGuard(UsesStep checkout) {
  checkout.getCallee() = "actions/checkout" and
  (
    checkout.getMajorVersion() = 7
    or
    unsafePrCheckoutGuardDataModel(checkout.getCallee(), checkout.getVersion())
  )
}

private predicate unsafePrCheckoutGuardEnabled(UsesStep checkout) {
  not exists(checkout.getArgument("allow-unsafe-pr-checkout"))
  or
  checkout.getArgument("allow-unsafe-pr-checkout").trim().toLowerCase() = ["", "false"]
}

private predicate runtimeGuardRecognizesCheckout(UsesStep checkout, Event event) {
  checkout.getArgument("ref").regexpMatch("refs/pull/[0-9]+/(head|merge)")
  or
  event.getName() = "pull_request_target" and
  (
    normalizeExpr(checkout.getArgument("ref"))
        .regexpMatch(".*\\bgithub\\.event\\.pull_request\\.(head\\.sha|merge_commit_sha)\\b.*")
    or
    normalizeExpr(checkout.getArgument("repository"))
        .regexpMatch(".*\\bgithub\\.event\\.pull_request\\.head\\.repo\\.full_name\\b.*")
  )
  or
  event.getName() = "workflow_run" and
  (
    normalizeExpr(checkout.getArgument("ref"))
        .regexpMatch(".*\\bgithub\\.event\\.workflow_run\\.(head_commit\\.id|head_sha)\\b.*")
    or
    normalizeExpr(checkout.getArgument("repository"))
        .regexpMatch(".*\\bgithub\\.event\\.workflow_run\\.head_repository\\.full_name\\b.*")
  )
}

/**
 * Holds if `checkout` refuses to check out fork pull request code for `event` at runtime.
 */
predicate runtimeGuardPreventsCheckout(Step checkout, Event event) {
  exists(UsesStep step |
    step = checkout and
    hasUnsafePrCheckoutGuard(step) and
    unsafePrCheckoutGuardEnabled(step) and
    step.getATriggerEvent() = event and
    event.getName() = ["pull_request_target", "workflow_run"] and
    runtimeGuardRecognizesCheckout(step, event)
  )
}

/** Holds if `checkout` can execute for at least one statically known trigger. */
predicate mayExecuteUnsafeCheckout(Step checkout) {
  not exists(checkout.getATriggerEvent())
  or
  exists(Event event |
    checkout.getATriggerEvent() = event and
    not runtimeGuardPreventsCheckout(checkout, event)
  )
}

/**
 * A taint-tracking configuration for PR HEAD references flowing
 * into actions/checkout's ref argument.
 */
private module ActionsMutableRefCheckoutConfig implements DataFlow::ConfigSig {
  predicate isSource(DataFlow::Node source) {
    (
      // remote flow sources
      source instanceof GitHubCtxSource
      or
      source instanceof GitHubEventCtxSource
      or
      source instanceof GitHubEventJsonSource
      or
      source instanceof MaDSource
      or
      // `ref` argument contains the PR id/number or head ref
      exists(Expression e |
        source.asExpr() = e and
        (
          containsHeadRef(e.getExpression()) or
          containsPullRequestNumber(e.getExpression())
        )
      )
      or
      // 3rd party actions returning the PR head ref
      exists(StepsExpression e, UsesStep step |
        source.asExpr() = e and
        e.getStepId() = step.getId() and
        (
          step.getCallee() = "eficode/resolve-pr-refs" and e.getFieldName() = "head_ref"
          or
          step.getCallee() = "xt0rted/pull-request-comment-branch" and e.getFieldName() = "head_ref"
          or
          step.getCallee() = "alessbell/pull-request-comment-branch" and
          e.getFieldName() = "head_ref"
          or
          step.getCallee() = "gotson/pull-request-comment-branch" and e.getFieldName() = "head_ref"
          or
          step.getCallee() = "potiuk/get-workflow-origin" and
          e.getFieldName() = ["sourceHeadBranch", "pullRequestNumber"]
          or
          step.getCallee() = "github/branch-deploy" and e.getFieldName() = ["ref", "fork_ref"]
        )
      )
    )
  }

  predicate isSink(DataFlow::Node sink) {
    exists(Uses uses |
      uses.getCallee() = "actions/checkout" and
      uses.getArgumentExpr(["ref", "repository"]) = sink.asExpr()
    )
  }

  predicate isAdditionalFlowStep(DataFlow::Node pred, DataFlow::Node succ) {
    exists(Run run |
      pred instanceof FileSource and
      pred.asExpr().(Step).getAFollowingStep() = run and
      succ.asExpr() = run.getScript() and
      exists(run.getScript().getAFileReadCommand())
    )
  }
}

module ActionsMutableRefCheckoutFlow = TaintTracking::Global<ActionsMutableRefCheckoutConfig>;

private module ActionsSHACheckoutConfig implements DataFlow::ConfigSig {
  predicate isSource(DataFlow::Node source) {
    source.asExpr().getATriggerEvent().getName() =
      ["pull_request_target", "workflow_run", "workflow_call", "issue_comment"] and
    (
      // `ref` argument contains the PR head/merge commit sha
      exists(Expression e |
        source.asExpr() = e and
        containsHeadSHA(e.getExpression())
      )
      or
      // 3rd party actions returning the PR head sha
      exists(StepsExpression e, UsesStep step |
        source.asExpr() = e and
        e.getStepId() = step.getId() and
        (
          step.getCallee() = "eficode/resolve-pr-refs" and e.getFieldName() = "head_sha"
          or
          step.getCallee() = "xt0rted/pull-request-comment-branch" and e.getFieldName() = "head_sha"
          or
          step.getCallee() = "alessbell/pull-request-comment-branch" and
          e.getFieldName() = "head_sha"
          or
          step.getCallee() = "gotson/pull-request-comment-branch" and e.getFieldName() = "head_sha"
          or
          step.getCallee() = "potiuk/get-workflow-origin" and
          e.getFieldName() = ["sourceHeadSha", "mergeCommitSha"]
        )
      )
    )
  }

  predicate isSink(DataFlow::Node sink) {
    exists(Uses uses |
      uses.getCallee() = "actions/checkout" and
      uses.getArgumentExpr(["ref", "repository"]) = sink.asExpr()
    )
  }

  predicate isAdditionalFlowStep(DataFlow::Node pred, DataFlow::Node succ) {
    exists(Run run |
      pred instanceof FileSource and
      pred.asExpr().(Step).getAFollowingStep() = run and
      succ.asExpr() = run.getScript() and
      exists(run.getScript().getAFileReadCommand())
    )
  }
}

module ActionsSHACheckoutFlow = TaintTracking::Global<ActionsSHACheckoutConfig>;

bindingset[s]
predicate containsPullRequestNumber(string s) {
  exists(
    normalizeExpr(s)
        .regexpFind([
            "\\bgithub\\.event\\.number\\b", "\\bgithub\\.event\\.issue\\.number\\b",
            "\\bgithub\\.event\\.pull_request\\.id\\b",
            "\\bgithub\\.event\\.pull_request\\.number\\b",
            "\\bgithub\\.event\\.check_suite\\.pull_requests\\[\\d+\\]\\.id\\b",
            "\\bgithub\\.event\\.check_suite\\.pull_requests\\[\\d+\\]\\.number\\b",
            "\\bgithub\\.event\\.check_run\\.check_suite\\.pull_requests\\[\\d+\\]\\.id\\b",
            "\\bgithub\\.event\\.check_run\\.check_suite\\.pull_requests\\[\\d+\\]\\.number\\b",
            "\\bgithub\\.event\\.check_run\\.pull_requests\\[\\d+\\]\\.id\\b",
            "\\bgithub\\.event\\.check_run\\.pull_requests\\[\\d+\\]\\.number\\b",
            // heuristics
            "\\bpr_number\\b", "\\bpr_id\\b"
          ], _, _)
  )
}

bindingset[s]
predicate containsHeadSHA(string s) {
  exists(
    normalizeExpr(s)
        .regexpFind([
            "\\bgithub\\.event\\.pull_request\\.head\\.sha\\b",
            "\\bgithub\\.event\\.pull_request\\.merge_commit_sha\\b",
            "\\bgithub\\.event\\.workflow_run\\.head_commit\\.id\\b",
            "\\bgithub\\.event\\.workflow_run\\.head_sha\\b",
            "\\bgithub\\.event\\.check_suite\\.after\\b",
            "\\bgithub\\.event\\.check_suite\\.head_commit\\.id\\b",
            "\\bgithub\\.event\\.check_suite\\.head_sha\\b",
            "\\bgithub\\.event\\.check_suite\\.pull_requests\\[\\d+\\]\\.head\\.sha\\b",
            "\\bgithub\\.event\\.check_run\\.check_suite\\.after\\b",
            "\\bgithub\\.event\\.check_run\\.check_suite\\.head_commit\\.id\\b",
            "\\bgithub\\.event\\.check_run\\.check_suite\\.head_sha\\b",
            "\\bgithub\\.event\\.check_run\\.check_suite\\.pull_requests\\[\\d+\\]\\.head\\.sha\\b",
            "\\bgithub\\.event\\.check_run\\.head_sha\\b",
            "\\bgithub\\.event\\.check_run\\.pull_requests\\[\\d+\\]\\.head\\.sha\\b",
            "\\bgithub\\.event\\.merge_group\\.head_sha\\b",
            "\\bgithub\\.event\\.merge_group\\.head_commit\\.id\\b",
            // heuristics
            "\\bhead\\.sha\\b", "\\bhead_sha\\b", "\\bmerge_sha\\b", "\\bpr_head_sha\\b"
          ], _, _)
  )
}

bindingset[s]
predicate containsHeadRef(string s) {
  exists(
    normalizeExpr(s)
        .regexpFind([
            "\\bgithub\\.event\\.pull_request\\.head\\.ref\\b", "\\bgithub\\.head_ref\\b",
            "\\bgithub\\.event\\.workflow_run\\.head_branch\\b",
            "\\bgithub\\.event\\.check_suite\\.pull_requests\\[\\d+\\]\\.head\\.ref\\b",
            "\\bgithub\\.event\\.check_run\\.check_suite\\.pull_requests\\[\\d+\\]\\.head\\.ref\\b",
            "\\bgithub\\.event\\.check_run\\.pull_requests\\[\\d+\\]\\.head\\.ref\\b",
            "\\bgithub\\.event\\.merge_group\\.head_ref\\b",
            // heuristics
            "\\bhead\\.ref\\b", "\\bhead_ref\\b", "\\bmerge_ref\\b", "\\bpr_head_ref\\b",
            // env vars
            "GITHUB_HEAD_REF",
          ], _, _)
  )
}

class SimplePRHeadCheckoutStep extends Step {
  SimplePRHeadCheckoutStep() {
    // This should be:
    // artifact instanceof PRHeadCheckoutStep
    // but PRHeadCheckoutStep uses Taint Tracking anc causes a non-Monolitic Recursion error
    // so we list all the subclasses of PRHeadCheckoutStep here and use actions/checkout as a workaround
    // instead of using ActionsMutableRefCheckout and ActionsSHACheckout
    exists(Uses uses |
      this = uses and
      uses.getCallee() = "actions/checkout" and
      exists(uses.getArgument("ref")) and
      not uses.getArgument("ref").matches("%base%") and
      uses.getATriggerEvent().getName() = checkoutTriggers() and
      mayExecuteUnsafeCheckout(this)
    )
    or
    this instanceof GitMutableRefCheckout
    or
    this instanceof GitSHACheckout
    or
    this instanceof GhMutableRefCheckout
    or
    this instanceof GhSHACheckout
  }
}

/** Checkout of a Pull Request HEAD */
abstract class PRHeadCheckoutStep extends Step {
  abstract string getPath();
}

/** Checkout of a Pull Request HEAD ref */
abstract class MutableRefCheckoutStep extends PRHeadCheckoutStep { }

/** Checkout of a Pull Request HEAD ref */
abstract class SHACheckoutStep extends PRHeadCheckoutStep { }

/**
 * Holds if `checkout` may retrieve pull request code that changed after an approval for `event`.
 *
 * Mutable references can change after any approval. An `issue_comment` payload does not contain
 * the pull request head SHA, so even an immutable head SHA must be resolved after the triggering
 * comment and may already identify code that was pushed after the approval. A label retained by a
 * `synchronize` or `reopened` event can likewise authorize a new immutable SHA that was never
 * reviewed.
 */
predicate mayCheckoutCodeChangedAfterApproval(PRHeadCheckoutStep checkout, Event event) {
  checkout instanceof MutableRefCheckoutStep
  or
  checkout instanceof SHACheckoutStep and
  (
    event.getName() = "issue_comment"
    or
    exists(LabelIfCheck check | hasStalePullRequestLabelAuthorization(checkout, event, check))
  )
}

/** Gets `reference` or a job output expression transitively referenced by it. */
private AstNode getShaReferenceFragment(AstNode reference) {
  result = reference
  or
  exists(NeedsExpression access, Outputs outputs, Expression output |
    access = reference.getAChildNode*() and
    outputs = access.getTarget() and
    output = outputs.getOutputExpr(access.getFieldName()) and
    result = getShaReferenceFragment(output)
  )
}

/** Gets a step that produced the SHA referenced by `reference`. */
private Step getShaProducer(AstNode reference) {
  exists(AstNode fragment, StepsExpression access |
    fragment = getShaReferenceFragment(reference) and
    access = fragment.getAChildNode*() and
    result = access.getTarget()
  )
}

/** Holds if every reference fragment is bound to a step or a resolvable job output. */
private predicate hasOnlyBoundShaReferences(AstNode reference) {
  not exists(AstNode fragment, SimpleReferenceExpression access |
    fragment = getShaReferenceFragment(reference) and
    access = fragment.getAChildNode*() and
    not access.getTarget() instanceof Step and
    not exists(Outputs outputs |
      outputs = access.getTarget() and
      exists(outputs.getOutputExpr(access.getFieldName()))
    )
  )
}

/** Holds if `producer` must run no later than `checkStep` for `event`. */
private predicate producerPrecedesCheck(Step producer, Step checkStep, Event event) {
  producer = checkStep
  or
  IntegratedCfg::orderedStepsMayReachForEvent(producer, checkStep, event)
  or
  producer.getEnclosingJob() != checkStep.getEnclosingJob() and
  JobSync::jobExecutionRequiresSuccessfulCompletionOf(checkStep.getEnclosingJob(),
    producer.getEnclosingJob(), event)
}

/** Holds if the SHA used by `checkout` was captured no later than `check`. */
private predicate shaCapturedNoLaterThanCheck(
  SHACheckoutStep checkout, CommentVsHeadDateCheck check, Event event
) {
  exists(AstNode reference, Step checkStep |
    reference = getCheckoutReference(checkout) and
    checkStep = check and
    hasOnlyBoundShaReferences(reference) and
    exists(getShaProducer(reference)) and
    not exists(Step producer |
      producer = getShaProducer(reference) and
      not producerPrecedesCheck(producer, checkStep, event)
    )
  )
}

/**
 * Holds if `checkout` has effective protection against code changing after approval.
 *
 * A comment-versus-head date check protects an immutable SHA captured no later than that check.
 * It does not protect a SHA resolved after the check or a mutable reference, either of which can
 * identify code pushed after the check.
 */
predicate hasEffectiveCheckoutTOCTOUProtection(PRHeadCheckoutStep checkout, Event event) {
  exists(ControlCheck check |
    check.protects(checkout, event, "untrusted-checkout-toctou") and
    (
      not check instanceof CommentVsHeadDateCheck
      or
      checkout instanceof SHACheckoutStep and
      not checkout instanceof MutableRefCheckoutStep and
      shaCapturedNoLaterThanCheck(checkout, check, event)
    )
  )
}

/** Holds if an effective authorization control protects `checkout` for `event`. */
predicate hasEffectiveCheckoutAuthorization(PRHeadCheckoutStep checkout, Event event) {
  exists(ControlCheck check | check.protects(checkout, event, "untrusted-checkout"))
}

private predicate isStalePullRequestApprovalTrigger(Event event) {
  event.getName() = "pull_request_target" and
  event.getAnActivityType() = ["synchronize", "reopened"]
}

/**
 * Holds if `check` is an effective label authorization that can be retained after the pull request
 * code changes.
 */
private predicate hasStalePullRequestLabelAuthorization(
  PRHeadCheckoutStep checkout, Event event, LabelIfCheck check
) {
  isStalePullRequestApprovalTrigger(event) and
  check.protects(checkout, event, "untrusted-checkout") and
  not Conditions::conditionRequiresPullRequestRepositoryCheck(check)
}

/** Holds if `check` is a recognized authorization attempt that does not protect `checkout`. */
predicate knownImproperCheckoutAuthorization(
  PRHeadCheckoutStep checkout, Event event, AuthorizationAttemptCheck check
) {
  // Only classify checks on events for which authorization controls model an external actor.
  event.getName() = any_event() and
  check.appliesToEvent(event) and
  check.dominates(checkout, event) and
  (
    not check.protects(checkout, event, "untrusted-checkout")
    or
    check instanceof PullRequestTargetRepositoryIfCheck and
    not Conditions::conditionRequiresPullRequestRepositoryCheck(check)
    or
    check instanceof WorkflowRunRepositoryIfCheck and
    not Conditions::conditionRequiresPullRequestRepositoryCheck(check)
  )
}

private predicate isClassifiableCheckout(PRHeadCheckoutStep checkout, Event event) {
  checkout.getATriggerEvent() = event and
  event.getName() = [checkoutTriggers(), "pull_request"] and
  IntegratedCfg::mayExecuteForEvent(checkout, event) and
  not runtimeGuardPreventsCheckout(checkout, event)
}

/** Holds if `checkout` is classified as an improper-access-control case for `event`. */
predicate classifiedAsImproperAccessControl(PRHeadCheckoutStep checkout, Event event) {
  isClassifiableCheckout(checkout, event) and
  exists(AuthorizationAttemptCheck check | knownImproperCheckoutAuthorization(checkout, event, check))
}

/** Holds if `checkout` is authorized but insufficiently bound to the approved revision. */
predicate classifiedAsUntrustedCheckoutTOCTOU(PRHeadCheckoutStep checkout, Event event) {
  isClassifiableCheckout(checkout, event) and
  not classifiedAsImproperAccessControl(checkout, event) and
  // The checkout has ordinary actor/access control protection.
  hasEffectiveCheckoutAuthorization(checkout, event) and
  mayCheckoutCodeChangedAfterApproval(checkout, event) and
  // The ordinary protection does not effectively bind approval to the checked-out revision.
  not hasEffectiveCheckoutTOCTOUProtection(checkout, event)
}

/**
 * Holds if no effective authorization protects `checkout` for `event`.
 *
 * For `issue_comment`, actor/access controls authorize the comment. A date comparison only checks
 * freshness and therefore does not turn an otherwise untrusted checkout into an authorized one.
 * The same ordinary-authorization rule applies to non-`issue_comment` trigger events.
 */
predicate classifiedAsUntrustedCheckout(PRHeadCheckoutStep checkout, Event event) {
  isClassifiableCheckout(checkout, event) and
  not classifiedAsImproperAccessControl(checkout, event) and
  not hasEffectiveCheckoutAuthorization(checkout, event)
}

/** Holds if `checkout` has effective authorization and revision binding for `event`. */
predicate classifiedAsProtectedCheckout(PRHeadCheckoutStep checkout, Event event) {
  isClassifiableCheckout(checkout, event) and
  not classifiedAsImproperAccessControl(checkout, event) and
  hasEffectiveCheckoutAuthorization(checkout, event) and
  (
    not mayCheckoutCodeChangedAfterApproval(checkout, event)
    or
    hasEffectiveCheckoutTOCTOUProtection(checkout, event)
  )
}

/** Gets the single security classification of `checkout` for `event`. */
string getCheckoutSecurityClassification(PRHeadCheckoutStep checkout, Event event) {
  classifiedAsImproperAccessControl(checkout, event) and result = "improper-access-control"
  or
  classifiedAsUntrustedCheckoutTOCTOU(checkout, event) and result = "toctou"
  or
  classifiedAsUntrustedCheckout(checkout, event) and result = "untrusted-checkout"
  or
  classifiedAsProtectedCheckout(checkout, event) and result = "protected"
}

/** Holds if `poisonable` is known to execute code from `checkout` for `event`. */
predicate checkoutMayLeadToCodeExecution(
  PRHeadCheckoutStep checkout, PoisonableStep poisonable, Event event
) {
  // The checkout is followed by a known poisonable step.
  checkout.getAFollowingStep() = poisonable and
  IntegratedCfg::orderedStepsMayReachForEvent(checkout, poisonable, event) and
  (
    poisonable instanceof Run and
    (
      // Check if the poisonable step is a local script execution step and the path of the command
      // or script matches the path of the downloaded code.
      isSubpath(poisonable.(LocalScriptExecutionRunStep).getPath(), checkout.getPath())
      or
      // Checking the working directory for non-local script execution steps is very difficult.
      not poisonable instanceof LocalScriptExecutionRunStep
      // It is not easy to extract the path from a non-local script execution step, so skip this
      // check for now:
      // isSubpath(poisonable.(Run).getWorkingDirectory(), checkout.getPath())
    )
    or
    poisonable instanceof UsesStep and
    (
      not poisonable instanceof LocalActionUsesStep and
      checkout.getPath() = "GITHUB_WORKSPACE/"
      or
      isSubpath(poisonable.(LocalActionUsesStep).getPath(), checkout.getPath())
    )
  )
}

private predicate criticalSeverityCheckout(
  PRHeadCheckoutStep checkout, PoisonableStep poisonable, Event event
) {
  // The checked-out code may lead to arbitrary code execution.
  checkoutMayLeadToCodeExecution(checkout, poisonable, event) and
  // The checkout and execution both occur in a privileged context.
  inPrivilegedContext(checkout, event) and
  inPrivilegedContext(poisonable, event)
}

private predicate highSeverityCheckout(PRHeadCheckoutStep checkout, Event event) {
  IntegratedCfg::mayExecuteForEvent(checkout, event) and
  // The checkout occurs in a privileged context.
  inPrivilegedContext(checkout, event) and
  // There is no evidence that the checked-out code is executed.
  not exists(PoisonableStep poisonable |
    checkoutMayLeadToCodeExecution(checkout, poisonable, event)
  )
}

/** Holds if `checkout` forms a critical ordinary untrusted-checkout finding. */
predicate criticalSeverityUntrustedCheckout(
  PRHeadCheckoutStep checkout, PoisonableStep poisonable, Event event
) {
  classifiedAsUntrustedCheckout(checkout, event) and
  criticalSeverityCheckout(checkout, poisonable, event) and
  // No effective control between checkout and execution protects the poisonable step.
  not exists(ControlCheck check | check.protects(poisonable, event, "untrusted-checkout"))
}

/** Holds if `checkout` forms a high ordinary untrusted-checkout finding. */
predicate highSeverityUntrustedCheckout(PRHeadCheckoutStep checkout, Event event) {
  classifiedAsUntrustedCheckout(checkout, event) and
  highSeverityCheckout(checkout, event)
}

/** Holds if `checkout` forms a medium ordinary untrusted-checkout finding. */
predicate mediumSeverityUntrustedCheckout(PRHeadCheckoutStep checkout) {
  // The checkout occurs in a non-privileged context.
  inNonPrivilegedContext(checkout) and
  mayExecuteUnsafeCheckout(checkout) and
  (
    exists(Event event | classifiedAsUntrustedCheckout(checkout, event))
    or
    // Reusable workflows without a modeled caller may not expose a concrete trigger event. Keep
    // the medium query conservative in that case, as it was before classification was shared.
    not exists(Event event | isClassifiableCheckout(checkout, event))
  )
}

/**
 * Holds if `checkout` and `poisonable` form a critical untrusted-checkout TOCTOU finding for
 * `event`.
 */
predicate criticalSeverityUntrustedCheckoutTOCTOU(
  PRHeadCheckoutStep checkout, PoisonableStep poisonable, Event event
) {
  classifiedAsUntrustedCheckoutTOCTOU(checkout, event) and
  criticalSeverityCheckout(checkout, poisonable, event)
}

bindingset[checkout, event]
pragma[inline_late]
private predicate hasDownstreamCriticalFindingForSameReference(
  PRHeadCheckoutStep checkout, Event event
) {
  exists(PRHeadCheckoutStep criticalCheckout, PoisonableStep poisonable |
    getCheckoutReferenceText(getCheckoutReference(criticalCheckout)) =
      getCheckoutReferenceText(getCheckoutReference(checkout)) and
    IntegratedCfg::mayReachForEvent(checkout, criticalCheckout, event) and
    criticalSeverityUntrustedCheckoutTOCTOU(criticalCheckout, poisonable, event)
  )
}

/** Holds if `checkout` forms a high untrusted-checkout TOCTOU finding for `event`. */
predicate highSeverityUntrustedCheckoutTOCTOU(PRHeadCheckoutStep checkout, Event event) {
  classifiedAsUntrustedCheckoutTOCTOU(checkout, event) and
  highSeverityCheckout(checkout, event) and
  not hasDownstreamCriticalFindingForSameReference(checkout, event) and
  not exists(PoisonableStep poisonable |
    criticalSeverityUntrustedCheckoutTOCTOU(checkout, poisonable, event)
  )
}

/** Checkout of a Pull Request HEAD ref using actions/checkout action */
class ActionsMutableRefCheckout extends MutableRefCheckoutStep instanceof UsesStep {
  ActionsMutableRefCheckout() {
    this.getCallee() = "actions/checkout" and
    (
      exists(
        ActionsMutableRefCheckoutFlow::PathNode source, ActionsMutableRefCheckoutFlow::PathNode sink
      |
        ActionsMutableRefCheckoutFlow::flowPath(source, sink) and
        this.getArgumentExpr(["ref", "repository"]) = sink.getNode().asExpr()
      )
      or
      // heuristic base on the step id and field name
      exists(string value, Expression expr |
        value.regexpMatch(".*(head|branch|ref).*") and
        not value.regexpMatch(".*(sha|commit).*") and
        expr = this.getArgumentExpr("ref")
      |
        expr.(StepsExpression).getStepId() = value
        or
        expr.(SimpleReferenceExpression).getFieldName() = value and
        not expr instanceof GitHubExpression and
        not expr instanceof MatrixExpression
        or
        expr.(NeedsExpression).getNeededJobId() = value
        or
        expr.(JsonReferenceExpression).getAccessPath() = value
        or
        expr.(JsonReferenceExpression).getInnerExpression() = value
      )
    )
  }

  override string getPath() {
    if exists(this.(UsesStep).getArgument("path"))
    then result = this.(UsesStep).getArgument("path")
    else result = "GITHUB_WORKSPACE/"
  }
}

/** Checkout of a Pull Request HEAD ref using actions/checkout action */
class ActionsSHACheckout extends SHACheckoutStep instanceof UsesStep {
  ActionsSHACheckout() {
    this.getCallee() = "actions/checkout" and
    (
      exists(ActionsSHACheckoutFlow::PathNode source, ActionsSHACheckoutFlow::PathNode sink |
        ActionsSHACheckoutFlow::flowPath(source, sink) and
        this.getArgumentExpr(["ref", "repository"]) = sink.getNode().asExpr()
      )
      or
      // heuristic base on the step id and field name
      exists(string value, Expression expr |
        value.regexpMatch(".*(sha|commit).*") and expr = this.getArgumentExpr("ref")
      |
        expr.(StepsExpression).getStepId() = value
        or
        expr.(SimpleReferenceExpression).getFieldName() = value and
        not expr instanceof GitHubExpression and
        not expr instanceof MatrixExpression
        or
        expr.(NeedsExpression).getNeededJobId() = value
        or
        expr.(JsonReferenceExpression).getAccessPath() = value
        or
        expr.(JsonReferenceExpression).getInnerExpression() = value
      )
    )
  }

  override string getPath() {
    if exists(this.(UsesStep).getArgument("path"))
    then result = this.(UsesStep).getArgument("path")
    else result = "GITHUB_WORKSPACE/"
  }
}

/** Checkout of a Pull Request HEAD ref using git within a Run step */
class GitMutableRefCheckout extends MutableRefCheckoutStep instanceof Run {
  GitMutableRefCheckout() {
    exists(string cmd | this.getScript().getACommand() = cmd |
      cmd.regexpMatch("git\\s+(fetch|pull).*") and
      (
        (containsHeadRef(cmd) or containsPullRequestNumber(cmd))
        or
        exists(string varname, string expr |
          expr = this.getInScopeEnvVarExpr(varname).getExpression() and
          (
            containsHeadRef(expr) or
            containsPullRequestNumber(expr)
          ) and
          exists(cmd.regexpFind(varname, _, _))
        )
      )
    )
  }

  override string getPath() { result = this.(Run).getWorkingDirectory() }
}

/** Checkout of a Pull Request HEAD ref using git within a Run step */
class GitSHACheckout extends SHACheckoutStep instanceof Run {
  GitSHACheckout() {
    exists(string cmd | this.getScript().getACommand() = cmd |
      cmd.regexpMatch("git\\s+(fetch|pull).*") and
      (
        containsHeadSHA(cmd)
        or
        exists(string varname, string expr |
          expr = this.getInScopeEnvVarExpr(varname).getExpression() and
          containsHeadSHA(expr) and
          exists(cmd.regexpFind(varname, _, _))
        )
      )
    )
  }

  override string getPath() { result = this.(Run).getWorkingDirectory() }
}

/** Checkout of a Pull Request HEAD ref using gh within a Run step */
class GhMutableRefCheckout extends MutableRefCheckoutStep instanceof Run {
  GhMutableRefCheckout() {
    exists(string cmd | this.getScript().getACommand() = cmd |
      cmd.regexpMatch(".*(gh|hub)\\s+pr\\s+checkout.*") and
      (
        (containsHeadRef(cmd) or containsPullRequestNumber(cmd))
        or
        exists(string varname |
          (
            containsHeadRef(this.getInScopeEnvVarExpr(varname).getExpression()) or
            containsPullRequestNumber(this.getInScopeEnvVarExpr(varname).getExpression())
          ) and
          exists(cmd.regexpFind(varname, _, _))
        )
      )
    )
  }

  override string getPath() { result = this.(Run).getWorkingDirectory() }
}

/** Checkout of a Pull Request HEAD ref using gh within a Run step */
class GhSHACheckout extends SHACheckoutStep instanceof Run {
  GhSHACheckout() {
    exists(string cmd | this.getScript().getACommand() = cmd |
      cmd.regexpMatch("gh\\s+pr\\s+checkout.*") and
      (
        containsHeadSHA(cmd)
        or
        exists(string varname |
          containsHeadSHA(this.getInScopeEnvVarExpr(varname).getExpression()) and
          exists(cmd.regexpFind(varname, _, _))
        )
      )
    )
  }

  override string getPath() { result = this.(Run).getWorkingDirectory() }
}

private predicate isRunCheckoutReference(
  PRHeadCheckoutStep checkout, Expression reference, string variable
) {
  checkout instanceof Run and
  reference = checkout.(Run).getInScopeEnvVarExpr(variable) and
  (
    checkout instanceof SHACheckoutStep and containsHeadSHA(reference.getExpression())
    or
    checkout instanceof MutableRefCheckoutStep and
    (
      containsHeadRef(reference.getExpression()) or
      containsPullRequestNumber(reference.getExpression())
    )
  ) and
  exists(string command |
    checkout.(Run).getScript().getACommand() = command and
    exists(command.regexpFind(variable, _, _))
  )
}

/** Gets the expression that controls the untrusted checkout, if one can be identified. */
AstNode getCheckoutReference(PRHeadCheckoutStep checkout) {
  exists(UsesStep uses |
    checkout = uses and
    (
      result = uses.getArgumentExpr("ref")
      or
      not exists(uses.getArgumentExpr("ref")) and result = uses.getArgumentExpr("repository")
    )
  )
  or
  exists(string variable | isRunCheckoutReference(checkout, result, variable))
  or
  checkout instanceof Run and
  result = checkout and
  not exists(Expression reference, string variable |
    isRunCheckoutReference(checkout, reference, variable)
  )
}

/** Gets a display label for the expression that controls the untrusted checkout. */
string getCheckoutReferenceText(AstNode reference) {
  result = reference.(Expression).toString()
  or
  not reference instanceof Expression and result = "the checkout command"
}

/** Adds checkout-reference provenance before the checkout step in path queries. */
predicate checkoutReferenceEdge(AstNode predecessor, AstNode successor) {
  exists(PRHeadCheckoutStep checkout |
    predecessor = getCheckoutReference(checkout) and
    successor = checkout and
    not predecessor = successor
  )
}
