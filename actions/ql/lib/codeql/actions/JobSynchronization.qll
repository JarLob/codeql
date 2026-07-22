/** Provides a synchronization DAG for GitHub Actions jobs and their `needs` dependencies. */

import codeql.actions.Ast
import codeql.actions.Cfg as Cfg
import codeql.actions.ExpressionEvaluation

private newtype TJobStatus =
  TSuccessStatus() or
  TFailureStatus() or
  TCancelledStatus() or
  TSkippedStatus()

/** A possible conclusion of an Actions job. */
abstract class JobStatus extends TJobStatus {
  abstract string getName();

  string toString() { result = this.getName() }
}

class SuccessStatus extends JobStatus, TSuccessStatus {
  override string getName() { result = "success" }
}

class FailureStatus extends JobStatus, TFailureStatus {
  override string getName() { result = "failure" }
}

class CancelledStatus extends JobStatus, TCancelledStatus {
  override string getName() { result = "cancelled" }
}

class SkippedStatus extends JobStatus, TSkippedStatus {
  override string getName() { result = "skipped" }
}

private newtype TNeedsStatus =
  TNeedsStatusSummary(boolean hasFailure, boolean hasCancellation, boolean hasSkip) {
    hasFailure in [false, true] and
    hasCancellation in [false, true] and
    hasSkip in [false, true]
  }

/** A summary of all conclusions observed at a `needs` synchronization join. */
class NeedsStatus extends TNeedsStatus {
  boolean hasFailure() { this = TNeedsStatusSummary(result, _, _) }

  boolean hasCancellation() { this = TNeedsStatusSummary(_, result, _) }

  boolean hasSkip() { this = TNeedsStatusSummary(_, _, result) }

  predicate isSuccess() { this = TNeedsStatusSummary(false, false, false) }

  private int getANonSuccessKind() {
    this.hasFailure() = true and result = 0
    or
    this.hasCancellation() = true and result = 1
    or
    this.hasSkip() = true and result = 2
  }

  int getNonSuccessKindCount() { result = count(this.getANonSuccessKind()) }

  string getName() {
    this = TNeedsStatusSummary(false, false, false) and result = "success"
    or
    this = TNeedsStatusSummary(true, false, false) and result = "failure"
    or
    this = TNeedsStatusSummary(false, true, false) and result = "cancelled"
    or
    this = TNeedsStatusSummary(false, false, true) and result = "skipped"
    or
    this = TNeedsStatusSummary(true, true, false) and result = "failure+cancelled"
    or
    this = TNeedsStatusSummary(true, false, true) and result = "failure+skipped"
    or
    this = TNeedsStatusSummary(false, true, true) and result = "cancelled+skipped"
    or
    this = TNeedsStatusSummary(true, true, true) and result = "failure+cancelled+skipped"
  }

  string toString() { result = this.getName() }
}

private predicate jobMayBeSkipped(Job job) { exists(job.getIf()) or exists(job.getANeededJob()) }

private predicate isRootJob(Job job) { not exists(job.getANeededJob()) }

private Job getANeededAncestor(Job job) { result = job.getANeededJob+() }

private predicate needsStatusMayOccur(Job job, NeedsStatus status) {
  isRootJob(job) and status.isSuccess()
  or
  not isRootJob(job) and
  status.getNonSuccessKindCount() <= count(getANeededAncestor(job)) and
  (
    status.hasSkip() = false
    or
    status.hasSkip() = true and
    exists(Job ancestor | ancestor = getANeededAncestor(job) and jobMayBeSkipped(ancestor))
  )
}

private newtype TNode =
  TWorkflowEntryNode(Workflow workflow) or
  TNeedsJoinNode(Job job) { exists(job.getANeededJob()) } or
  TJobDecisionNode(Job job, NeedsStatus needsStatus) { needsStatusMayOccur(job, needsStatus) } or
  TJobExecutionNode(Job job) or
  TJobCompletionNode(Job job, JobStatus status) {
    not status instanceof SkippedStatus or jobMayBeSkipped(job)
  } or
  TWorkflowExitNode(Workflow workflow)

/** A node in the job synchronization DAG. */
abstract class Node extends TNode {
  /**
   * Gets an immediate synchronization successor. Incoming arcs of a `NeedsJoinNode` and a
   * `WorkflowExitNode` are conjunctive synchronization requirements, not alternative paths.
   */
  Node getASuccessor() { synchronizationSuccessor(this, result) }

  /** Gets an immediate synchronization successor feasible for `event`. */
  Node getASuccessor(Event event) { synchronizationSuccessorForEvent(this, result, event) }

  /** Gets an immediate synchronization predecessor. */
  Node getAPredecessor() { result.getASuccessor() = this }

  /** Gets an immediate synchronization predecessor feasible for `event`. */
  Node getAPredecessor(Event event) { result.getASuccessor(event) = this }

  /**
   * Gets a structurally downstream synchronization node, including this node. This relation does
   * not imply that one incoming arc alone releases a conjunctive join.
   */
  Node getAReachableNode() { result = this or result = this.getASuccessor+() }

  /** Gets a structurally downstream node after event-specific decision pruning. */
  Node getAReachableNode(Event event) { synchronizationReachableForEvent(this, result, event) }

  abstract string toString();
}

/** Entry into all root jobs of a workflow. */
class WorkflowEntryNode extends Node, TWorkflowEntryNode {
  Workflow workflow;

  WorkflowEntryNode() { this = TWorkflowEntryNode(workflow) }

  Workflow getWorkflow() { result = workflow }

  override string toString() { result = "enter jobs in " + workflow.toString() }
}

/** An AND-join that waits for every job named by `needs`. */
class NeedsJoinNode extends Node, TNeedsJoinNode {
  Job job;

  NeedsJoinNode() { this = TNeedsJoinNode(job) }

  Job getJob() { result = job }

  Job getARequiredJob() { result = job.getANeededJob() }

  JobCompletionNode getARequiredCompletion() { result.getJob() = this.getARequiredJob() }

  override string toString() { result = "join needs for " + job.getId() }
}

/** Evaluation of a job's explicit condition and implicit dependency status check. */
class JobDecisionNode extends Node, TJobDecisionNode {
  Job job;
  NeedsStatus needsStatus;

  JobDecisionNode() { this = TJobDecisionNode(job, needsStatus) }

  Job getJob() { result = job }

  /** Gets the aggregate conclusion of this job's prerequisites. */
  NeedsStatus getNeedsStatus() { result = needsStatus }

  override string toString() {
    result = "decide " + job.getId() + " after " + needsStatus.toString()
  }
}

/** Execution of a job after its synchronization and condition checks succeed. */
class JobExecutionNode extends Node, TJobExecutionNode {
  Job job;

  JobExecutionNode() { this = TJobExecutionNode(job) }

  Job getJob() { result = job }

  Cfg::Node getCfgNode() { result.getAstNode() = job }

  override string toString() { result = "execute " + job.getId() }
}

/** Completion of a job with a specific conclusion. */
class JobCompletionNode extends Node, TJobCompletionNode {
  Job job;
  JobStatus status;

  JobCompletionNode() { this = TJobCompletionNode(job, status) }

  Job getJob() { result = job }

  JobStatus getStatus() { result = status }

  override string toString() { result = "complete " + job.getId() + " as " + status.toString() }
}

/** A conjunctive exit join reached after every terminal job in a workflow completes. */
class WorkflowExitNode extends Node, TWorkflowExitNode {
  Workflow workflow;

  WorkflowExitNode() { this = TWorkflowExitNode(workflow) }

  Workflow getWorkflow() { result = workflow }

  override string toString() { result = "exit jobs in " + workflow.toString() }
}

private predicate isTerminalJob(Job job) {
  not exists(Job dependent | dependent.getANeededJob() = job)
}

private predicate decisionMayHaveOutcome(Job job, boolean outcome) {
  not exists(job.getIf()) and
  isRootJob(job) and
  outcome = true
  or
  not exists(job.getIf()) and
  not isRootJob(job) and
  outcome in [false, true]
  or
  exists(job.getIf()) and outcome in [false, true]
}

private predicate ownConditionMayHaveOutcome(Job job, Event event, boolean outcome) {
  not exists(job.getIf()) and outcome = true
  or
  exists(If condition |
    condition = job.getIf() and
    (
      exists(condition.getConditionExpr().getRoot()) and
      mayEvaluateConditionToBoolean(condition, condition.getConditionExpr().getRoot(), event,
        outcome)
      or
      not exists(condition.getConditionExpr().getRoot()) and outcome in [false, true]
    )
  )
}

private predicate decisionMayHaveOutcome(
  Job job, Event event, NeedsStatus needsStatus, boolean outcome
) {
  isRootJob(job) and
  ownConditionMayHaveOutcome(job, event, outcome)
  or
  not isRootJob(job) and
  not exists(job.getIf()) and
  (
    needsStatus.isSuccess() and outcome = true
    or
    not needsStatus.isSuccess() and outcome = false
  )
  or
  not isRootJob(job) and
  exists(If condition |
    condition = job.getIf() and
    (
      exists(condition.getConditionExpr().getRoot()) and
      hasStatusCheckFunction(condition) and
      mayEvaluateConditionToBooleanAfterNeedsState(condition,
        condition.getConditionExpr().getRoot(), event, needsStatus.hasFailure(),
        needsStatus.hasCancellation(), needsStatus.hasSkip(), outcome)
      or
      exists(condition.getConditionExpr().getRoot()) and
      not hasStatusCheckFunction(condition) and
      (
        needsStatus.isSuccess() and
        mayEvaluateConditionToBoolean(condition, condition.getConditionExpr().getRoot(), event,
          outcome)
        or
        not needsStatus.isSuccess() and outcome = false
      )
      or
      not exists(condition.getConditionExpr().getRoot()) and
      (
        needsStatus.isSuccess() and outcome in [false, true]
        or
        not needsStatus.isSuccess() and outcome = false
      )
    )
  )
}

private Job getNeededJobAt(Job job, int index) {
  result =
    rank[index + 1](Job needed | needed = job.getANeededJob() | needed order by needed.getId())
}

private string getStatusCode(JobStatus status) {
  status instanceof SuccessStatus and result = "s"
  or
  status instanceof FailureStatus and result = "f"
  or
  status instanceof CancelledStatus and result = "c"
  or
  status instanceof SkippedStatus and result = "k"
}

bindingset[code]
private JobStatus getStatusForCode(string code) {
  code = "s" and result instanceof SuccessStatus
  or
  code = "f" and result instanceof FailureStatus
  or
  code = "c" and result instanceof CancelledStatus
  or
  code = "k" and result instanceof SkippedStatus
}

private string getANeededStatusAssignmentPrefix(Job job, Event event, int length) {
  length = 0 and result = ""
  or
  exists(string prefix, Job needed, JobStatus status |
    length > 0 and
    needed = getNeededJobAt(job, length - 1) and
    jobMayCompleteForEvent(needed, event, status) and
    prefix = getANeededStatusAssignmentPrefix(job, event, length - 1) and
    result = prefix + getStatusCode(status)
  )
}

private string getANeededStatusAssignment(Job job, Event event) {
  result = getANeededStatusAssignmentPrefix(job, event, count(job.getANeededJob()))
}

bindingset[job, assignment, needed]
private JobStatus getAssignedStatus(Job job, string assignment, Job needed) {
  exists(int index |
    needed = getNeededJobAt(job, index) and
    result = getStatusForCode(assignment.charAt(index))
  )
}

private predicate statusFlags(
  JobStatus status, boolean hasFailure, boolean hasCancellation, boolean hasSkip
) {
  status instanceof SuccessStatus and
  hasFailure = false and
  hasCancellation = false and
  hasSkip = false
  or
  status instanceof FailureStatus and
  hasFailure = true and
  hasCancellation = false and
  hasSkip = false
  or
  status instanceof CancelledStatus and
  hasFailure = false and
  hasCancellation = true and
  hasSkip = false
  or
  status instanceof SkippedStatus and
  hasFailure = false and
  hasCancellation = false and
  hasSkip = true
}

bindingset[before, added]
private predicate mergeFlag(boolean before, boolean added, boolean after) {
  after = true and
  (before = true or added = true)
  or
  after = false and before = false and added = false
}

bindingset[assignment, code]
private predicate assignmentContains(string assignment, string code, boolean outcome) {
  exists(assignment.indexOf(code)) and outcome = true
  or
  not exists(assignment.indexOf(code)) and outcome = false
}

bindingset[assignment]
private NeedsStatus getAssignmentSummary(string assignment) {
  exists(boolean hasFailure, boolean hasCancellation, boolean hasSkip |
    assignmentContains(assignment, "f", hasFailure) and
    assignmentContains(assignment, "c", hasCancellation) and
    assignmentContains(assignment, "k", hasSkip) and
    result = TNeedsStatusSummary(hasFailure, hasCancellation, hasSkip)
  )
}

private predicate neededStatusSummaryPrefix(
  Job job, Event event, int length, boolean hasFailure, boolean hasCancellation, boolean hasSkip
) {
  length = 0 and
  hasFailure = false and
  hasCancellation = false and
  hasSkip = false
  or
  exists(
    boolean previousFailure, boolean previousCancellation, boolean previousSkip,
    boolean addedFailure, boolean addedCancellation, boolean addedSkip, Job needed, JobStatus status
  |
    length > 0 and
    needed = getNeededJobAt(job, length - 1) and
    jobMayCompleteForEvent(needed, event, status) and
    statusFlags(status, addedFailure, addedCancellation, addedSkip) and
    neededStatusSummaryPrefix(job, event, length - 1, previousFailure, previousCancellation,
      previousSkip) and
    mergeFlag(previousFailure, addedFailure, hasFailure) and
    mergeFlag(previousCancellation, addedCancellation, hasCancellation) and
    mergeFlag(previousSkip, addedSkip, hasSkip)
  )
}

private predicate needsStatusMayOccurForEvent(Job job, Event event, NeedsStatus status) {
  exists(boolean hasFailure, boolean hasCancellation, boolean hasSkip |
    neededStatusSummaryPrefix(job, event, count(job.getANeededJob()), hasFailure, hasCancellation,
      hasSkip) and
    status = TNeedsStatusSummary(hasFailure, hasCancellation, hasSkip)
  )
}

private string getStringLiteralValue(ExpressionNode node) {
  node instanceof LiteralExpression and
  node.getKind() = "StringLiteral" and
  result =
    node.(LiteralExpression)
        .getValue()
        .substring(1, node.(LiteralExpression).getValue().length() - 1)
        .regexpReplaceAll("''", "'")
}

bindingset[node, job, assignment]
private string getAssignedStringValue(ExpressionNode node, Job job, string assignment) {
  result = getStringLiteralValue(node)
  or
  exists(AccessExpression access, Job needed |
    access = node and
    needed = job.getANeededJob() and
    access.getAccessPath() = "needs." + needed.getId() + ".result" and
    result = getAssignedStatus(job, assignment, needed).getName()
  )
}

bindingset[left, operator, right]
private predicate compareAssignedStrings(string left, string operator, string right, boolean outcome) {
  operator = "==" and left.toLowerCase() = right.toLowerCase() and outcome = true
  or
  operator = "==" and left.toLowerCase() != right.toLowerCase() and outcome = false
  or
  operator = "!=" and left.toLowerCase() != right.toLowerCase() and outcome = true
  or
  operator = "!=" and left.toLowerCase() = right.toLowerCase() and outcome = false
}

private predicate containsAssignedNeedsResult(ExpressionNode node, Job job) {
  exists(AccessExpression access, Job needed |
    access = node.getAChild*() and
    needed = job.getANeededJob() and
    access.getAccessPath() = "needs." + needed.getId() + ".result"
  )
}

private predicate jobConditionContainsAssignedNeedsResult(Job job) {
  exists(If condition |
    condition = job.getIf() and
    exists(condition.getConditionExpr().getRoot()) and
    containsAssignedNeedsResult(condition.getConditionExpr().getRoot(), job)
  )
}

private predicate belongsToAssignedNeedsResultCondition(ExpressionNode node) {
  exists(Job job, If condition |
    condition = job.getIf() and
    node.getExpression() = condition.getConditionExpr() and
    jobConditionContainsAssignedNeedsResult(job)
  )
}

private predicate mayEvaluateForNeedsStatus(ExpressionNode node, NeedsStatus status, boolean outcome) {
  belongsToAssignedNeedsResultCondition(node) and
  (
    node instanceof ExpressionRoot and
    mayEvaluateForNeedsStatus(node.getChild(0), status, outcome)
    or
    node instanceof LiteralExpression and
    node.getKind() = "BooleanLiteral" and
    node.(LiteralExpression).getValue().toLowerCase() = outcome.toString()
    or
    node instanceof UnaryExpression and
    node.(UnaryExpression).getOperator() = "!" and
    mayEvaluateForNeedsStatus(node.(UnaryExpression).getOperand(), status, outcome.booleanNot())
    or
    node instanceof BinaryExpression and
    node.(BinaryExpression).getOperator() = "&&" and
    (
      outcome = false and
      mayEvaluateForNeedsStatus([
          node.(BinaryExpression).getLeftOperand(), node.(BinaryExpression).getRightOperand()
        ], status, false)
      or
      outcome = true and
      mayEvaluateForNeedsStatus(node.(BinaryExpression).getLeftOperand(), status, true) and
      mayEvaluateForNeedsStatus(node.(BinaryExpression).getRightOperand(), status, true)
    )
    or
    node instanceof BinaryExpression and
    node.(BinaryExpression).getOperator() = "||" and
    (
      outcome = true and
      mayEvaluateForNeedsStatus([
          node.(BinaryExpression).getLeftOperand(), node.(BinaryExpression).getRightOperand()
        ], status, true)
      or
      outcome = false and
      mayEvaluateForNeedsStatus(node.(BinaryExpression).getLeftOperand(), status, false) and
      mayEvaluateForNeedsStatus(node.(BinaryExpression).getRightOperand(), status, false)
    )
    or
    node instanceof FunctionCallExpression and
    not exists(node.(FunctionCallExpression).getArgument(_)) and
    (
      node.(FunctionCallExpression).getCallee().getName().toLowerCase() = "always" and
      outcome = true
      or
      node.(FunctionCallExpression).getCallee().getName().toLowerCase() = "success" and
      (
        status.isSuccess() and outcome = true
        or
        not status.isSuccess() and outcome = false
      )
      or
      node.(FunctionCallExpression).getCallee().getName().toLowerCase() = "failure" and
      outcome = status.hasFailure()
      or
      node.(FunctionCallExpression).getCallee().getName().toLowerCase() = "cancelled" and
      outcome = status.hasCancellation()
    )
    or
    not node instanceof ExpressionRoot and
    not node instanceof UnaryExpression and
    not (
      node instanceof BinaryExpression and
      node.(BinaryExpression).getOperator() = ["&&", "||"]
    ) and
    not (node instanceof LiteralExpression and node.getKind() = "BooleanLiteral") and
    not (
      node instanceof FunctionCallExpression and
      not exists(node.(FunctionCallExpression).getArgument(_)) and
      node.(FunctionCallExpression).getCallee().getName().toLowerCase() =
        ["always", "success", "failure", "cancelled"]
    ) and
    outcome in [false, true]
  )
}

private predicate mayEvaluateForAssignment(
  ExpressionNode node, Job job, Event event, string assignment, boolean outcome
) {
  exists(If condition |
    condition = job.getIf() and
    node.getExpression() = condition.getConditionExpr() and
    condition.getATriggerEvent() = event
  ) and
  assignment = getAConservativeNeededStatusAssignment(job) and
  (
    not containsAssignedNeedsResult(node, job) and
    exists(NeedsStatus status |
      status = getAssignmentSummary(assignment) and
      mayEvaluateForNeedsStatus(node, status, outcome)
    )
    or
    node instanceof ExpressionRoot and
    mayEvaluateForAssignment(node.getChild(0), job, event, assignment, outcome)
    or
    node instanceof UnaryExpression and
    mayEvaluateForAssignment(node.(UnaryExpression).getOperand(), job, event, assignment,
      outcome.booleanNot())
    or
    node instanceof BinaryExpression and
    node.(BinaryExpression).getOperator() = "&&" and
    (
      outcome = false and
      mayEvaluateForAssignment([
          node.(BinaryExpression).getLeftOperand(), node.(BinaryExpression).getRightOperand()
        ], job, event, assignment, false)
      or
      outcome = true and
      mayEvaluateForAssignment(node.(BinaryExpression).getLeftOperand(), job, event, assignment,
        true) and
      mayEvaluateForAssignment(node.(BinaryExpression).getRightOperand(), job, event, assignment,
        true)
    )
    or
    node instanceof BinaryExpression and
    node.(BinaryExpression).getOperator() = "||" and
    (
      outcome = true and
      mayEvaluateForAssignment([
          node.(BinaryExpression).getLeftOperand(), node.(BinaryExpression).getRightOperand()
        ], job, event, assignment, true)
      or
      outcome = false and
      mayEvaluateForAssignment(node.(BinaryExpression).getLeftOperand(), job, event, assignment,
        false) and
      mayEvaluateForAssignment(node.(BinaryExpression).getRightOperand(), job, event, assignment,
        false)
    )
    or
    node instanceof BinaryExpression and
    node.(BinaryExpression).getOperator() = ["==", "!="] and
    compareAssignedStrings(getAssignedStringValue(node.(BinaryExpression).getLeftOperand(), job,
        assignment), node.(BinaryExpression).getOperator(),
      getAssignedStringValue(node.(BinaryExpression).getRightOperand(), job, assignment), outcome)
    or
    node instanceof BinaryExpression and
    node.(BinaryExpression).getOperator() = ["==", "!="] and
    (
      not exists(getAssignedStringValue(node.(BinaryExpression).getLeftOperand(), job, assignment))
      or
      not exists(getAssignedStringValue(node.(BinaryExpression).getRightOperand(), job, assignment))
    ) and
    outcome in [false, true]
    or
    node instanceof AccessExpression and
    exists(getAssignedStringValue(node, job, assignment)) and
    outcome = true
    or
    containsAssignedNeedsResult(node, job) and
    not node instanceof ExpressionRoot and
    not node instanceof UnaryExpression and
    not node instanceof BinaryExpression and
    not node instanceof AccessExpression and
    outcome in [false, true]
  )
}

private string getAConservativeNeededStatusAssignmentPrefix(Job job, int length) {
  length = 0 and result = ""
  or
  exists(string prefix, Job needed, JobStatus status |
    length > 0 and
    needed = getNeededJobAt(job, length - 1) and
    (not status instanceof SkippedStatus or jobMayBeSkipped(needed)) and
    prefix = getAConservativeNeededStatusAssignmentPrefix(job, length - 1) and
    result = prefix + getStatusCode(status)
  )
}

private string getAConservativeNeededStatusAssignment(Job job) {
  result = getAConservativeNeededStatusAssignmentPrefix(job, count(job.getANeededJob()))
}

private predicate summaryIncludesStatus(NeedsStatus summary, JobStatus status) {
  status instanceof SuccessStatus
  or
  status instanceof FailureStatus and summary.hasFailure() = true
  or
  status instanceof CancelledStatus and summary.hasCancellation() = true
  or
  status instanceof SkippedStatus and summary.hasSkip() = true
}

bindingset[job, event, assignment]
private predicate decisionMayHaveOutcomeForAssignment(
  Job job, Event event, string assignment, boolean outcome
) {
  isRootJob(job) and ownConditionMayHaveOutcome(job, event, outcome)
  or
  not isRootJob(job) and
  not exists(job.getIf()) and
  (
    getAssignmentSummary(assignment).isSuccess() and outcome = true
    or
    not getAssignmentSummary(assignment).isSuccess() and outcome = false
  )
  or
  not isRootJob(job) and
  exists(If condition |
    condition = job.getIf() and
    (
      exists(condition.getConditionExpr().getRoot()) and
      hasStatusCheckFunction(condition) and
      mayEvaluateForAssignment(condition.getConditionExpr().getRoot(), job, event, assignment,
        outcome)
      or
      exists(condition.getConditionExpr().getRoot()) and
      not hasStatusCheckFunction(condition) and
      (
        getAssignmentSummary(assignment).isSuccess() and
        mayEvaluateForAssignment(condition.getConditionExpr().getRoot(), job, event, assignment,
          outcome)
        or
        not getAssignmentSummary(assignment).isSuccess() and outcome = false
      )
      or
      not exists(condition.getConditionExpr().getRoot()) and
      (
        getAssignmentSummary(assignment).isSuccess() and outcome in [false, true]
        or
        not getAssignmentSummary(assignment).isSuccess() and outcome = false
      )
    )
  )
}

/** Holds if `job` may execute for `event`, accounting for all transitive prerequisites. */
bindingset[job, event]
predicate jobMayExecuteForEvent(Job job, Event event) {
  job.getATriggerEvent() = event and
  (
    not jobConditionContainsAssignedNeedsResult(job) and
    exists(NeedsStatus needsStatus |
      needsStatusMayOccurForEvent(job, event, needsStatus) and
      decisionMayHaveOutcome(job, event, needsStatus, true)
    )
    or
    jobConditionContainsAssignedNeedsResult(job) and
    exists(string assignment |
      assignment = getANeededStatusAssignment(job, event) and
      decisionMayHaveOutcomeForAssignment(job, event, assignment, true)
    )
  )
}

/** Holds if `job` may complete with `status` for `event`. */
bindingset[job, event]
predicate jobMayCompleteForEvent(Job job, Event event, JobStatus status) {
  job.getATriggerEvent() = event and
  (
    jobMayExecuteForEvent(job, event) and not status instanceof SkippedStatus
    or
    status instanceof SkippedStatus and
    (
      not jobConditionContainsAssignedNeedsResult(job) and
      exists(NeedsStatus needsStatus |
        needsStatusMayOccurForEvent(job, event, needsStatus) and
        decisionMayHaveOutcome(job, event, needsStatus, false)
      )
      or
      jobConditionContainsAssignedNeedsResult(job) and
      exists(string assignment |
        assignment = getANeededStatusAssignment(job, event) and
        decisionMayHaveOutcomeForAssignment(job, event, assignment, false)
      )
    )
  )
}

private predicate jobMayExecuteWithDirectNeededStatus(
  Job job, Event event, Job neededJob, JobStatus neededStatus
) {
  neededJob = job.getANeededJob() and
  job.getATriggerEvent() = event and
  (
    not jobConditionContainsAssignedNeedsResult(job) and
    exists(NeedsStatus status |
      summaryIncludesStatus(status, neededStatus) and
      decisionMayHaveOutcome(job, event, status, true)
    )
    or
    jobConditionContainsAssignedNeedsResult(job) and
    exists(string assignment |
      assignment = getAConservativeNeededStatusAssignment(job) and
      getAssignedStatus(job, assignment, neededJob) = neededStatus and
      decisionMayHaveOutcomeForAssignment(job, event, assignment, true)
    )
  )
}

private predicate jobExecutionDirectlyRequiresSuccessfulCompletionOf(
  Job job, Job neededJob, Event event
) {
  exists(JobStatus status | jobMayExecuteWithDirectNeededStatus(job, event, neededJob, status)) and
  not exists(JobStatus status |
    not status instanceof SuccessStatus and
    jobMayExecuteWithDirectNeededStatus(job, event, neededJob, status)
  )
}

/**
 * Holds if every execution of `job` for `event` requires `neededJob` to complete successfully.
 * `neededJob` may be a direct or transitive prerequisite.
 */
predicate jobExecutionRequiresSuccessfulCompletionOf(Job job, Job neededJob, Event event) {
  jobExecutionDirectlyRequiresSuccessfulCompletionOf(job, neededJob, event)
  or
  exists(Job directNeeded |
    directNeeded = job.getANeededJob() and
    jobExecutionDirectlyRequiresSuccessfulCompletionOf(job, directNeeded, event) and
    jobExecutionRequiresSuccessfulCompletionOf(directNeeded, neededJob, event)
  )
}

private predicate synchronizationSuccessor(Node predecessor, Node successor) {
  exists(WorkflowEntryNode entry, JobDecisionNode decision |
    predecessor = entry and
    decision.getJob().getWorkflow() = entry.getWorkflow() and
    isRootJob(decision.getJob()) and
    successor = decision
  )
  or
  exists(JobCompletionNode completion, NeedsJoinNode join |
    predecessor = completion and
    completion.getJob() = join.getARequiredJob() and
    successor = join
  )
  or
  exists(NeedsJoinNode join, JobDecisionNode decision |
    predecessor = join and decision.getJob() = join.getJob() and successor = decision
  )
  or
  exists(JobDecisionNode decision, JobExecutionNode execution |
    predecessor = decision and
    execution.getJob() = decision.getJob() and
    decisionMayHaveOutcome(decision.getJob(), true) and
    successor = execution
  )
  or
  exists(JobDecisionNode decision, JobCompletionNode completion |
    predecessor = decision and
    completion.getJob() = decision.getJob() and
    completion.getStatus() instanceof SkippedStatus and
    decisionMayHaveOutcome(decision.getJob(), false) and
    successor = completion
  )
  or
  exists(JobExecutionNode execution, JobCompletionNode completion |
    predecessor = execution and
    completion.getJob() = execution.getJob() and
    not completion.getStatus() instanceof SkippedStatus and
    successor = completion
  )
  or
  exists(JobCompletionNode completion, WorkflowExitNode exit |
    predecessor = completion and
    isTerminalJob(completion.getJob()) and
    completion.getJob().getWorkflow() = exit.getWorkflow() and
    successor = exit
  )
}

private predicate synchronizationSuccessorForEvent(Node predecessor, Node successor, Event event) {
  synchronizationSuccessor(predecessor, successor) and
  not predecessor instanceof JobDecisionNode and
  not predecessor instanceof NeedsJoinNode
  or
  exists(NeedsJoinNode join, JobDecisionNode decision |
    predecessor = join and
    decision.getJob() = join.getJob() and
    needsStatusMayOccurForEvent(decision.getJob(), event, decision.getNeedsStatus()) and
    successor = decision
  )
  or
  exists(JobDecisionNode decision, JobExecutionNode execution |
    predecessor = decision and
    execution.getJob() = decision.getJob() and
    decisionMayHaveOutcome(decision.getJob(), event, decision.getNeedsStatus(), true) and
    successor = execution
  )
  or
  exists(JobDecisionNode decision, JobCompletionNode completion |
    predecessor = decision and
    completion.getJob() = decision.getJob() and
    completion.getStatus() instanceof SkippedStatus and
    decisionMayHaveOutcome(decision.getJob(), event, decision.getNeedsStatus(), false) and
    successor = completion
  )
}

cached
private predicate synchronizationReachableForEvent(Node source, Node target, Event event) {
  target = source
  or
  exists(Node predecessor |
    synchronizationReachableForEvent(source, predecessor, event) and
    synchronizationSuccessorForEvent(predecessor, target, event)
  )
}

WorkflowEntryNode getEntryNode(Workflow workflow) { result = TWorkflowEntryNode(workflow) }

WorkflowExitNode getExitNode(Workflow workflow) { result = TWorkflowExitNode(workflow) }
