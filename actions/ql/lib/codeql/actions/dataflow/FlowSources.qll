private import codeql.actions.security.ArtifactDownloadSteps
private import codeql.actions.security.UntrustedCheckoutQuery
private import codeql.actions.config.Config
private import codeql.actions.DataFlow
private import codeql.actions.dataflow.ExternalFlow

/**
 * A data flow source.
 */
abstract class SourceNode extends DataFlow::Node {
  /**
   * Gets a string that represents the source kind with respect to threat modeling.
   */
  abstract string getThreatModel();
}

/** A data flow source of remote user input. */
abstract class RemoteFlowSource extends SourceNode {
  /** Gets a string that describes the type of this remote flow source. */
  abstract string getSourceType();

  /** Gets the event that triggered the source. */
  abstract string getEventName();

  override string getThreatModel() { result = "remote" }
}

/**
 * A data flow source of user input from github context.
 * eg: github.head_ref
 */
class GitHubCtxSource extends RemoteFlowSource {
  string flag;
  string event;

  GitHubCtxSource() {
    exists(GitHubExpression e |
      this.asExpr() = e and
      // github.head_ref
      e.getFieldName() = "head_ref" and
      flag = "branch"
    |
      event = e.getATriggerEvent().getName() and
      event = "pull_request_target"
      or
      not exists(e.getATriggerEvent()) and
      event = "unknown"
    )
  }

  override string getSourceType() { result = flag }

  override string getEventName() { result = event }
}

bindingset[expression]
private predicate parsedUntrustedEventProperty(Expression expression, string kind) {
  exists(AccessExpression access, string regexp |
    access.getExpression() = expression and
    untrustedEventPropertiesDataModel(regexp, kind) and
    not kind = "json" and
    access.getAccessPath().regexpMatch("(?i)" + wrapRegexp(regexp) + ".*") and
    normalizeExpr(expression.getExpression()).regexpMatch("(?i)\\s*" + wrapRegexp(regexp) + ".*")
  )
}

bindingset[expression, event]
private predicate parsedExpressionContainsEventContext(Expression expression, string event) {
  exists(AccessExpression access, string contextPrefix |
    access.getExpression() = expression and
    contextTriggerDataModel(event, contextPrefix) and
    access.getAccessPath().matches("%" + contextPrefix + "%")
  )
}

bindingset[expression]
private predicate unparsedUntrustedEventProperty(Expression expression, string kind) {
  not exists(expression.getRoot()) and
  exists(string regexp |
    untrustedEventPropertiesDataModel(regexp, kind) and
    not kind = "json" and
    normalizeExpr(expression.getExpression()).regexpMatch("(?i)\\s*" + wrapRegexp(regexp) + ".*")
  )
}

bindingset[expression, event]
private predicate unparsedExpressionContainsEventContext(Expression expression, string event) {
  not exists(expression.getRoot()) and
  exists(string contextPrefix |
    contextTriggerDataModel(event, contextPrefix) and
    normalizeExpr(expression.getExpression()).matches("%" + contextPrefix + "%")
  )
}

bindingset[node]
pragma[inline_late]
private predicate isProtectedWorkflowRunHeadAccess(ExpressionNode node) {
  exists(AccessExpression access, string path |
    node = access and
    path = access.getAccessPath().toLowerCase() and
    (
      path =
        [
          "github.event.workflow_run.head_branch", "github.event.workflow_run.head_sha",
          "github.event.workflow_run.head_commit", "github.event.workflow_run.head_repository"
        ]
      or
      path.matches("github.event.workflow_run.head_commit.%")
      or
      path.matches("github.event.workflow_run.head_repository.%")
    )
  )
}

bindingset[node]
pragma[inline_late]
private predicate spansWholeExpression(ExpressionNode node) {
  node.getStartOffset() = 0 and
  node.getEndOffset() = node.getExpression().getExpression().length()
}

bindingset[expression]
pragma[inline_late]
private predicate hasProtectedWorkflowRunHeadShape(Expression expression) {
  exists(AccessExpression access |
    access.getExpression() = expression and
    spansWholeExpression(access) and
    isProtectedWorkflowRunHeadAccess(access)
  )
  or
  exists(FunctionCallExpression call |
    call.getExpression() = expression and
    spansWholeExpression(call) and
    call.getCallee().getName().toLowerCase() = ["fromjson", "tojson"] and
    isProtectedWorkflowRunHeadAccess(call.getArgument(0)) and
    not exists(call.getArgument(1))
  )
}

/**
 * Holds if GitHub's positive `workflow_run.branches` filter guarantees that this value comes from
 * the base repository rather than a fork. Other workflow-run fields, such as `display_title` and
 * `pull_requests`, may still carry externally controlled data through base-repository events.
 */
private predicate isProtectedWorkflowRunHeadValue(Expression expression) {
  exists(Event event |
    expression.getATriggerEvent() = event and
    event.getName() = "workflow_run" and
    event.hasProperty("branches") and
    hasProtectedWorkflowRunHeadShape(expression)
  )
}

class GitHubEventCtxSource extends RemoteFlowSource {
  string flag;
  string context;
  string event;

  GitHubEventCtxSource() {
    exists(Expression e |
      this.asExpr() = e and
      not isProtectedWorkflowRunHeadValue(e) and
      context = e.getExpression() and
      (
        event = e.getATriggerEvent().getName() and
        (
          parsedExpressionContainsEventContext(e, event) and
          parsedUntrustedEventProperty(e, flag)
          or
          unparsedExpressionContainsEventContext(e, event) and
          unparsedUntrustedEventProperty(e, flag)
        )
        or
        not exists(e.getATriggerEvent()) and
        event = "unknown" and
        (parsedUntrustedEventProperty(e, flag) or unparsedUntrustedEventProperty(e, flag))
      )
    )
  }

  override string getSourceType() { result = flag }

  string getContext() { result = context }

  override string getEventName() { result = event }
}

abstract class CommandSource extends RemoteFlowSource {
  abstract string getCommand();

  abstract Run getEnclosingRun();

  override string getEventName() { result = this.getEnclosingRun().getATriggerEvent().getName() }
}

class GitCommandSource extends RemoteFlowSource, CommandSource {
  Run run;
  string cmd;
  string flag;

  GitCommandSource() {
    exists(Step checkout, string cmd_regex |
      checkout instanceof SimplePRHeadCheckoutStep and
      this.asExpr() = run.getScript() and
      checkout.getAFollowingStep() = run and
      run.getScript().getAStmt() = cmd and
      cmd.indexOf("git") = 0 and
      untrustedGitCommandDataModel(cmd_regex, flag) and
      cmd.regexpMatch(cmd_regex + ".*")
    )
  }

  override string getSourceType() { result = flag }

  override string getCommand() { result = cmd }

  override Run getEnclosingRun() { result = run }
}

class GhCLICommandSource extends RemoteFlowSource, CommandSource {
  Run run;
  string cmd;
  string flag;

  GhCLICommandSource() {
    exists(string cmd_regex |
      this.asExpr() = run.getScript() and
      run.getScript().getAStmt() = cmd and
      cmd.indexOf("gh ") = 0 and
      untrustedGhCommandDataModel(cmd_regex, flag) and
      cmd.regexpMatch(cmd_regex + ".*") and
      (
        cmd.regexpMatch(".*\\b(pr|pulls)\\b.*") and
        run.getATriggerEvent().getName() = checkoutTriggers()
        or
        not cmd.regexpMatch(".*\\b(pr|pulls)\\b.*")
      )
    )
  }

  override string getSourceType() { result = flag }

  override Run getEnclosingRun() { result = run }

  override string getCommand() { result = cmd }
}

class GitHubEventPathSource extends RemoteFlowSource, CommandSource {
  string cmd;
  string flag;
  Run run;

  // Examples
  // COMMENT_AUTHOR=$(jq -r .comment.user.login "$GITHUB_EVENT_PATH")
  // CURRENT_COMMENT=$(jq -r .comment.body "$GITHUB_EVENT_PATH")
  // PR_HEAD=$(jq --raw-output .pull_request.head.ref ${GITHUB_EVENT_PATH})
  // PR_NUMBER=$(jq --raw-output .pull_request.number ${GITHUB_EVENT_PATH})
  // PR_TITLE=$(jq --raw-output .pull_request.title ${GITHUB_EVENT_PATH})
  // BODY=$(jq -r '.issue.body' "$GITHUB_EVENT_PATH" | sed -n '3p')
  GitHubEventPathSource() {
    this.asExpr() = run.getScript() and
    run.getScript().getACommand() = cmd and
    cmd.matches("jq%") and
    cmd.matches("%GITHUB_EVENT_PATH%") and
    exists(string regexp, string access_path |
      untrustedEventPropertiesDataModel(regexp, flag) and
      not flag = "json" and
      access_path = "github.event" + cmd.regexpCapture(".*\\s+([^\\s]+)\\s+.*", 1) and
      normalizeExpr(access_path).regexpMatch("(?i)\\s*" + wrapRegexp(regexp) + ".*")
    )
  }

  override string getSourceType() { result = flag }

  override string getCommand() { result = cmd }

  override Run getEnclosingRun() { result = run }
}

bindingset[node]
private predicate isUntrustedEventPropertyNode(ExpressionNode node) {
  exists(string regexp |
    untrustedEventPropertiesDataModel(regexp, _) and
    normalizeExpr(node.getText()).regexpMatch("(?i)" + wrapRegexp(regexp))
  )
}

bindingset[expression, event]
private predicate parsedJsonSourceForEvent(Expression expression, string event) {
  exists(FunctionCallExpression call, ExpressionNode argument |
    call.getExpression() = expression and
    call.getCallee().getName().toLowerCase() = ["fromjson", "tojson"] and
    argument = call.getArgument(0) and
    (
      isUntrustedEventPropertyNode(argument) and
      exists(string contextPrefix |
        contextTriggerDataModel(event, contextPrefix) and
        normalizeExpr(argument.getText()).matches("%" + contextPrefix + "%")
      )
      or
      normalizeExpr(argument.getText()) = "github.event" and
      contextTriggerDataModel(event, _)
    )
  )
}

bindingset[expression, event]
private predicate unparsedJsonSourceForEvent(Expression expression, string event) {
  not exists(expression.getRoot()) and
  (
    exists(string context, string regexp, string contextPrefix |
      context = expression.getExpression() and
      untrustedEventPropertiesDataModel(regexp, _) and
      contextTriggerDataModel(event, contextPrefix) and
      normalizeExpr(context).matches("%" + contextPrefix + "%") and
      normalizeExpr(context).regexpMatch("(?i).*" + wrapJsonRegexp(regexp) + ".*")
    )
    or
    exists(string context |
      context = expression.getExpression() and
      contextTriggerDataModel(event, _) and
      normalizeExpr(context).regexpMatch("(?i).*" + wrapJsonRegexp("\\bgithub.event\\b") + ".*")
    )
  )
}

class GitHubEventJsonSource extends RemoteFlowSource {
  string flag;
  string event;

  GitHubEventJsonSource() {
    exists(Expression e |
      this.asExpr() = e and
      not isProtectedWorkflowRunHeadValue(e) and
      (
        event = e.getEnclosingWorkflow().getATriggerEvent().getName() and
        (parsedJsonSourceForEvent(e, event) or unparsedJsonSourceForEvent(e, event))
        or
        not exists(e.getATriggerEvent()) and
        event = "unknown" and
        exists(string property, string kind | untrustedEventPropertiesDataModel(property, kind))
      ) and
      flag = "json"
    )
  }

  override string getSourceType() { result = flag }

  override string getEventName() { result = event }
}

/**
 * A Source of untrusted data defined in a MaD specification
 */
class MaDSource extends RemoteFlowSource {
  string sourceType;

  MaDSource() { madSource(this, sourceType, _) }

  override string getSourceType() { result = sourceType }

  override string getEventName() { result = this.asExpr().getATriggerEvent().getName() }
}

abstract class FileSource extends RemoteFlowSource { }

/**
 * A downloaded artifact.
 */
class ArtifactSource extends RemoteFlowSource, FileSource {
  ArtifactSource() { this.asExpr() instanceof PotentiallyUntrustedArtifactDownloadStep }

  override string getSourceType() { result = "artifact" }

  override string getEventName() { result = this.asExpr().getATriggerEvent().getName() }
}

/**
 * A file from an untrusted checkout.
 */
private class CheckoutSource extends RemoteFlowSource, FileSource {
  CheckoutSource() { this.asExpr() instanceof SimplePRHeadCheckoutStep }

  override string getSourceType() { result = "artifact" }

  override string getEventName() { result = this.asExpr().getATriggerEvent().getName() }
}

/**
 * A list of file names returned by dorny/paths-filter.
 */
class DornyPathsFilterSource extends RemoteFlowSource {
  DornyPathsFilterSource() {
    exists(UsesStep u |
      u.getCallee() = "dorny/paths-filter" and
      u.getArgument("list-files") = ["csv", "json"] and
      this.asExpr() = u
    )
  }

  override string getSourceType() { result = "filename" }

  override string getEventName() { result = this.asExpr().getATriggerEvent().getName() }
}

/**
 * A list of file names returned by tj-actions/changed-files.
 */
class TJActionsChangedFilesSource extends RemoteFlowSource {
  TJActionsChangedFilesSource() {
    exists(UsesStep u, string vulnerable_action, string vulnerable_version, string vulnerable_sha |
      vulnerableActionsDataModel(vulnerable_action, vulnerable_version, vulnerable_sha, _) and
      u.getCallee() = "tj-actions/changed-files" and
      u.getCallee() = vulnerable_action and
      (
        u.getArgument("safe_output") = "false"
        or
        (u.getVersion() = vulnerable_version or u.getVersion() = vulnerable_sha)
      ) and
      this.asExpr() = u
    )
  }

  override string getSourceType() { result = "filename" }

  override string getEventName() { result = this.asExpr().getATriggerEvent().getName() }
}

/**
 * A list of file names returned by tj-actions/verify-changed-files.
 */
class TJActionsVerifyChangedFilesSource extends RemoteFlowSource {
  TJActionsVerifyChangedFilesSource() {
    exists(UsesStep u, string vulnerable_action, string vulnerable_version, string vulnerable_sha |
      vulnerableActionsDataModel(vulnerable_action, vulnerable_version, vulnerable_sha, _) and
      u.getCallee() = "tj-actions/verify-changed-files" and
      u.getCallee() = vulnerable_action and
      (
        u.getArgument("safe_output") = "false"
        or
        (u.getVersion() = vulnerable_version or u.getVersion() = vulnerable_sha)
      ) and
      this.asExpr() = u
    )
  }

  override string getSourceType() { result = "filename" }

  override string getEventName() { result = this.asExpr().getATriggerEvent().getName() }
}

class Xt0rtedSlashCommandSource extends RemoteFlowSource {
  Xt0rtedSlashCommandSource() {
    exists(UsesStep u |
      u.getCallee() = "xt0rted/slash-command-action" and
      u.getArgument("permission-level").toLowerCase() = ["read", "none"] and
      this.asExpr() = u
    )
  }

  override string getSourceType() { result = "text" }

  override string getEventName() { result = this.asExpr().getATriggerEvent().getName() }
}

class ZenteredIssueFormBodyParserSource extends RemoteFlowSource {
  ZenteredIssueFormBodyParserSource() {
    exists(UsesStep u |
      u.getCallee() = "zentered/issue-forms-body-parser" and
      not exists(u.getArgument("body")) and
      this.asExpr() = u
    )
  }

  override string getSourceType() { result = "text" }

  override string getEventName() { result = this.asExpr().getATriggerEvent().getName() }
}

class OctokitRequestActionSource extends RemoteFlowSource {
  OctokitRequestActionSource() {
    exists(UsesStep u, string route |
      u.getCallee() = "octokit/request-action" and
      route = u.getArgument("route").trim() and
      route.indexOf("GET") = 0 and
      (
        route.matches("%/commits%") or
        route.matches("%/comments%") or
        route.matches("%/pulls%") or
        route.matches("%/issues%") or
        route.matches("%/users%") or
        route.matches("%github.event.issue.pull_request.url%")
      ) and
      this.asExpr() = u
    )
  }

  override string getSourceType() { result = "text" }

  override string getEventName() { result = this.asExpr().getATriggerEvent().getName() }
}
