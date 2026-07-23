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

bindingset[expression]
private predicate getStaticContinueOnErrorValue(Expression expression, boolean outcome) {
  exists(LiteralExpression literal |
    literal = expression.getRoot().getChild(0) and
    literal.getKind() = "BooleanLiteral" and
    literal.getValue().toLowerCase() = outcome.toString()
  )
}

private predicate jobContinueOnErrorMayEvaluateTo(Job job, Event event, boolean outcome) {
  job.getATriggerEvent() = event and
  exists(string value |
    value = job.getContinueOnErrorValue() and
    (
      value.toLowerCase() = "true" and outcome = true
      or
      value.toLowerCase() = "false" and outcome = false
      or
      not value.toLowerCase() = ["true", "false"] and
      getStaticContinueOnErrorValue(job.getContinueOnErrorExpr(), outcome)
      or
      not value.toLowerCase() = ["true", "false"] and
      not exists(boolean known |
        getStaticContinueOnErrorValue(job.getContinueOnErrorExpr(), known)
      ) and
      outcome in [false, true]
    )
  )
  or
  not exists(job.getContinueOnErrorValue()) and outcome = false
}

private predicate stepContinueOnErrorMayEvaluateTo(Step step, Event event, boolean outcome) {
  step.getATriggerEvent() = event and
  exists(string value |
    value = step.getContinueOnErrorValue() and
    (
      value.toLowerCase() = "true" and outcome = true
      or
      value.toLowerCase() = "false" and outcome = false
      or
      not value.toLowerCase() = ["true", "false"] and
      getStaticContinueOnErrorValue(step.getContinueOnErrorExpr(), outcome)
      or
      not value.toLowerCase() = ["true", "false"] and
      not exists(boolean known |
        getStaticContinueOnErrorValue(step.getContinueOnErrorExpr(), known)
      ) and
      outcome in [false, true]
    )
  )
  or
  not exists(step.getContinueOnErrorValue()) and outcome = false
}

private predicate jobAlwaysContinuesOnError(Job job) {
  job.getContinueOnErrorValue().toLowerCase() = "true"
  or
  getStaticContinueOnErrorValue(job.getContinueOnErrorExpr(), true)
}

/** Gets a possible effective conclusion after applying a job's `continue-on-error`. */
bindingset[job, event, outcome]
JobStatus getAJobConclusionForOutcome(Job job, Event event, JobStatus outcome) {
  not outcome instanceof FailureStatus and result = outcome
  or
  outcome instanceof FailureStatus and
  jobContinueOnErrorMayEvaluateTo(job, event, false) and
  result instanceof FailureStatus
  or
  outcome instanceof FailureStatus and
  jobContinueOnErrorMayEvaluateTo(job, event, true) and
  result instanceof SuccessStatus
}

/** Gets a possible effective conclusion after applying a step's `continue-on-error`. */
bindingset[step, event, outcome]
JobStatus getAStepConclusionForOutcome(Step step, Event event, JobStatus outcome) {
  not outcome instanceof FailureStatus and result = outcome
  or
  outcome instanceof FailureStatus and
  stepContinueOnErrorMayEvaluateTo(step, event, false) and
  result instanceof FailureStatus
  or
  outcome instanceof FailureStatus and
  stepContinueOnErrorMayEvaluateTo(step, event, true) and
  result instanceof SuccessStatus
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

private ReusableWorkflow getCalledReusableWorkflow(Job job) {
  exists(ExternalJob caller |
    caller = job and result.getACaller() = caller
  )
}

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

private string getMatrixDimensionAt(Job job, int index) {
  result =
    rank[index + 1](string name | name = job.getStrategy().getAMatrixDimensionName() |
      name order by name
    )
}

private int getStaticMatrixInstanceCountPrefix(Job job, int length) {
  length = 0 and result = 1
  or
  exists(int previous, string dimension |
    length > 0 and
    dimension = getMatrixDimensionAt(job, length - 1) and
    previous = getStaticMatrixInstanceCountPrefix(job, length - 1) and
    result = previous * job.getStrategy().getMatrixDimensionValueCount(dimension)
  )
}

private int getStaticMatrixInstanceCount(Job job) {
  job.getStrategy().hasStaticCartesianMatrix() and
  result =
    getStaticMatrixInstanceCountPrefix(job, count(job.getStrategy().getAMatrixDimensionName()))
}

private string getAStaticMatrixAssignmentPrefix(Job job, int length) {
  length = 0 and result = ""
  or
  exists(string prefix, string dimension, int valueIndex |
    length > 0 and
    dimension = getMatrixDimensionAt(job, length - 1) and
    valueIndex in [0 .. job.getStrategy().getMatrixDimensionValueCount(dimension) - 1] and
    prefix = getAStaticMatrixAssignmentPrefix(job, length - 1) and
    (
      prefix = "" and result = dimension + "=" + valueIndex.toString()
      or
      prefix != "" and result = prefix + "," + dimension + "=" + valueIndex.toString()
    )
  )
}

private string getAMatrixAssignment(Job job) {
  getStaticMatrixInstanceCount(job) <= 256 and
  result =
    getAStaticMatrixAssignmentPrefix(job, count(job.getStrategy().getAMatrixDimensionName()))
  or
  job.getStrategy().hasMatrix() and
  not getStaticMatrixInstanceCount(job) <= 256 and
  result = "*"
}

private newtype TMatrixJobInstance =
  TConcreteMatrixJobInstance(Job job, string assignment) { assignment = getAMatrixAssignment(job) }

/** A concrete bounded expansion, or conservative wildcard expansion, of a matrix job. */
class MatrixJobInstance extends TMatrixJobInstance {
  Job getJob() { this = TConcreteMatrixJobInstance(result, _) }

  string getAssignment() { this = TConcreteMatrixJobInstance(_, result) }

  string toString() { result = this.getJob().getId() + "[" + this.getAssignment() + "]" }
}

private newtype TNode =
  TWorkflowEntryNode(Workflow workflow) or
  TNeedsJoinNode(Job job) { exists(job.getANeededJob()) } or
  TJobDecisionNode(Job job, NeedsStatus needsStatus) { needsStatusMayOccur(job, needsStatus) } or
  TJobExecutionNode(Job job) {
    not job.getStrategy().hasMatrix() and not exists(getCalledReusableWorkflow(job))
  } or
  TJobCompletionNode(Job job, JobStatus status) {
    (not job.getStrategy().hasMatrix() or status instanceof SkippedStatus) and
    not (status instanceof FailureStatus and jobAlwaysContinuesOnError(job)) and
    (not status instanceof SkippedStatus or jobMayBeSkipped(job))
  } or
  TMatrixJobExecutionNode(MatrixJobInstance instance) or
  TMatrixJobCompletionNode(MatrixJobInstance instance, JobStatus status) {
    not status instanceof SkippedStatus and
    not (status instanceof FailureStatus and jobAlwaysContinuesOnError(instance.getJob()))
  } or
  TMatrixJobFanInNode(Job job, JobStatus status) {
    job.getStrategy().hasMatrix() and
    not status instanceof SkippedStatus and
    not (status instanceof FailureStatus and jobAlwaysContinuesOnError(job))
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

  MatrixJobFanInNode getARequiredMatrixFanIn() { result.getJob() = this.getARequiredJob() }

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

/** Execution of one expansion of a matrix job. */
class MatrixJobExecutionNode extends Node, TMatrixJobExecutionNode {
  MatrixJobInstance instance;

  MatrixJobExecutionNode() { this = TMatrixJobExecutionNode(instance) }

  MatrixJobInstance getInstance() { result = instance }

  Job getJob() { result = instance.getJob() }

  Cfg::Node getCfgNode() { result.getAstNode() = this.getJob() }

  override string toString() { result = "execute " + instance.toString() }
}

/** Completion of one expansion of a matrix job. */
class MatrixJobCompletionNode extends Node, TMatrixJobCompletionNode {
  MatrixJobInstance instance;
  JobStatus status;

  MatrixJobCompletionNode() { this = TMatrixJobCompletionNode(instance, status) }

  MatrixJobInstance getInstance() { result = instance }

  Job getJob() { result = instance.getJob() }

  JobStatus getStatus() { result = status }

  override string toString() {
    result = "complete " + instance.toString() + " as " + status.toString()
  }
}

/** A conjunctive fan-in that exposes one aggregate conclusion for a matrix job. */
class MatrixJobFanInNode extends Node, TMatrixJobFanInNode {
  Job job;
  JobStatus status;

  MatrixJobFanInNode() { this = TMatrixJobFanInNode(job, status) }

  Job getJob() { result = job }

  JobStatus getStatus() { result = status }

  override string toString() { result = "fan in " + job.getId() + " as " + status.toString() }
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
  not isRootJob(job) and
  jobConditionContainsAssignedNeedsValue(job) and
  exists(string assignment |
    assignment = getANeededStatusAssignment(job, event) and
    getAssignmentSummary(assignment) = needsStatus and
    decisionMayHaveOutcomeForAssignment(job, event, assignment, outcome)
  )
  or
  not jobConditionContainsAssignedNeedsValue(job) and
  (
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

bindingset[job, assignment, needed]
private JobStatus getAssignedStatus(Job job, string assignment, Job needed) {
  exists(int index |
    needed = getNeededJobAt(job, index) and
    result = getStatusForCode(assignment.charAt(index))
  )
}

private Job getPrerequisiteAt(Job job, int index) {
  result =
    rank[index + 1](Job prerequisite, int depth |
      prerequisite = getANeededAncestor(job) and
      depth = count(prerequisite.getANeededJob+())
    |
      prerequisite order by depth, prerequisite.getId()
    )
}

bindingset[job, assignment, prerequisite]
private JobStatus getAssignedPrerequisiteStatus(
  Job job, string assignment, Job prerequisite
) {
  exists(int index |
    prerequisite = getPrerequisiteAt(job, index) and
    result = getStatusForCode(assignment.charAt(index))
  )
}

bindingset[job, prerequisite, prerequisiteAssignment]
private string getDirectAssignmentFromPrerequisites(
  Job job, Job prerequisite, string prerequisiteAssignment
) {
  result = concat(int index |
      index in [0 .. count(prerequisite.getANeededJob()) - 1]
    |
      getStatusCode(
        getAssignedPrerequisiteStatus(job, prerequisiteAssignment,
          getNeededJobAt(prerequisite, index))
      ), "" order by index
    )
}

bindingset[job, event, assignment]
private predicate decisionMayHaveOutcomeForExactAssignment(
  Job job, Event event, string assignment, boolean outcome
) {
  jobConditionContainsAssignedNeedsValue(job) and
  decisionMayHaveOutcomeForAssignment(job, event, assignment, outcome)
  or
  not jobConditionContainsAssignedNeedsValue(job) and
  decisionMayHaveOutcome(job, event, getAssignmentSummary(assignment), outcome)
}

bindingset[job, event, assignment]
private predicate jobMayCompleteForDirectAssignment(
  Job job, Event event, string assignment, JobStatus status
) {
  job.getATriggerEvent() = event and
  (
    status instanceof SkippedStatus and
    decisionMayHaveOutcomeForExactAssignment(job, event, assignment, false)
    or
    not status instanceof SkippedStatus and
    decisionMayHaveOutcomeForExactAssignment(job, event, assignment, true) and
    exists(JobStatus outcome |
      not outcome instanceof SkippedStatus and
      status = getAJobConclusionForOutcome(job, event, outcome)
    )
  )
}

private string getAReachablePrerequisiteAssignmentPrefix(Job job, Event event, int length) {
  length = 0 and result = ""
  or
  exists(string prefix, string directAssignment, Job prerequisite, JobStatus status |
    length > 0 and
    prerequisite = getPrerequisiteAt(job, length - 1) and
    prefix = getAReachablePrerequisiteAssignmentPrefix(job, event, length - 1) and
    directAssignment = getDirectAssignmentFromPrerequisites(job, prerequisite, prefix) and
    jobMayCompleteForDirectAssignment(prerequisite, event, directAssignment, status) and
    result = prefix + getStatusCode(status)
  )
}

private string getANeededStatusAssignment(Job job, Event event) {
  exists(string prerequisiteAssignment |
    prerequisiteAssignment =
      getAReachablePrerequisiteAssignmentPrefix(job, event, count(getANeededAncestor(job))) and
    result = concat(int index |
        index in [0 .. count(job.getANeededJob()) - 1]
      |
        getStatusCode(
          getAssignedPrerequisiteStatus(job, prerequisiteAssignment, getNeededJobAt(job, index))
        ), "" order by index
      )
  )
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

private predicate needsStatusMayOccurForEvent(Job job, Event event, NeedsStatus status) {
  exists(string assignment |
    assignment = getANeededStatusAssignment(job, event) and
    status = getAssignmentSummary(assignment)
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

private string getStaticExpressionOutputStringValue(Expression output) {
  result = getStringLiteralValue(output.getRoot().getChild(0))
  or
  output.getRoot().getChild(0) instanceof LiteralExpression and
  output.getRoot().getChild(0).getKind() = "BooleanLiteral" and
  result = output.getRoot().getChild(0).(LiteralExpression).getValue().toLowerCase()
  or
  output.getRoot().getChild(0) instanceof LiteralExpression and
  output.getRoot().getChild(0).getKind() = "NullLiteral" and
  result = ""
}

private string getStaticOutputStringValue(Job needed, string outputName) {
  result = getStaticExpressionOutputStringValue(needed.getOutputExpr(outputName))
  or
  not exists(needed.getOutputExpr(outputName)) and
  result = needed.getOutputs().getOutputValue(outputName)
}

bindingset[access, needed, outputName]
private predicate accessesNeededOutput(AccessExpression access, Job needed, string outputName) {
  access.getAccessPath().toLowerCase() =
    ("needs." + needed.getId() + ".outputs." + outputName).toLowerCase()
  or
  access.getAccessPath().toLowerCase() =
    ("needs." + needed.getId() + ".outputs['" + outputName + "']").toLowerCase()
}

private string getReferencedStaticOutputStringValue(ExpressionNode node, Job job, Job needed) {
  exists(AccessExpression access, string outputName |
    access = node and
    needed = job.getANeededJob() and
    outputName = needed.getOutputs().getAnOutputName() and
    accessesNeededOutput(access, needed, outputName) and
    result = getStaticOutputStringValue(needed, outputName)
  )
}

bindingset[node, job, assignment]
private string getAssignedOutputStringValue(ExpressionNode node, Job job, string assignment) {
  exists(Job needed, JobStatus status, string staticValue |
    staticValue = getReferencedStaticOutputStringValue(node, job, needed) and
    status = getAssignedStatus(job, assignment, needed) and
    (
      status instanceof SuccessStatus and result = staticValue
      or
      status instanceof FailureStatus and result = [staticValue, ""]
      or
      status instanceof CancelledStatus and result = [staticValue, ""]
      or
      status instanceof SkippedStatus and result = ""
    )
  )
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
  or
  result = getAssignedOutputStringValue(node, job, assignment)
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

private predicate containsAssignedNeedsValue(ExpressionNode node, Job job) {
  exists(AccessExpression access, Job needed |
    access = node.getAChild*() and
    needed = job.getANeededJob() and
    access.getAccessPath() = "needs." + needed.getId() + ".result"
  )
  or
  exists(ExpressionNode child, Job needed |
    child = node.getAChild*() and exists(getReferencedStaticOutputStringValue(child, job, needed))
  )
}

private predicate jobConditionContainsAssignedNeedsValue(Job job) {
  exists(If condition |
    condition = job.getIf() and
    exists(condition.getConditionExpr().getRoot()) and
    containsAssignedNeedsValue(condition.getConditionExpr().getRoot(), job)
  )
}

private predicate belongsToAssignedNeedsValueCondition(ExpressionNode node) {
  exists(Job job, If condition |
    condition = job.getIf() and
    node.getExpression() = condition.getConditionExpr() and
    jobConditionContainsAssignedNeedsValue(job)
  )
}

private predicate mayEvaluateForNeedsStatus(ExpressionNode node, NeedsStatus status, boolean outcome) {
  belongsToAssignedNeedsValueCondition(node) and
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
    not containsAssignedNeedsValue(node, job) and
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
    exists(string value | value = getAssignedStringValue(node, job, assignment) |
      value = "" and outcome = false
      or
      value != "" and outcome = true
    )
    or
    node instanceof AccessExpression and
    not exists(getAssignedStringValue(node, job, assignment)) and
    outcome in [false, true]
    or
    containsAssignedNeedsValue(node, job) and
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
    not jobConditionContainsAssignedNeedsValue(job) and
    exists(NeedsStatus needsStatus |
      needsStatusMayOccurForEvent(job, event, needsStatus) and
      decisionMayHaveOutcome(job, event, needsStatus, true)
    )
    or
    jobConditionContainsAssignedNeedsValue(job) and
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
    jobMayExecuteForEvent(job, event) and
    exists(JobStatus outcome |
      not outcome instanceof SkippedStatus and
      status = getAJobConclusionForOutcome(job, event, outcome)
    )
    or
    status instanceof SkippedStatus and
    (
      not jobConditionContainsAssignedNeedsValue(job) and
      exists(NeedsStatus needsStatus |
        needsStatusMayOccurForEvent(job, event, needsStatus) and
        decisionMayHaveOutcome(job, event, needsStatus, false)
      )
      or
      jobConditionContainsAssignedNeedsValue(job) and
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
  exists(string assignment |
    assignment = getANeededStatusAssignment(job, event) and
    getAssignedStatus(job, assignment, neededJob) = neededStatus and
    decisionMayHaveOutcomeForExactAssignment(job, event, assignment, true)
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
  exists(MatrixJobFanInNode fanIn, NeedsJoinNode join |
    predecessor = fanIn and
    fanIn.getJob() = join.getARequiredJob() and
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
  exists(JobDecisionNode decision, WorkflowEntryNode entry |
    predecessor = decision and
    entry.getWorkflow() = getCalledReusableWorkflow(decision.getJob()) and
    decisionMayHaveOutcome(decision.getJob(), true) and
    successor = entry
  )
  or
  exists(JobDecisionNode decision, MatrixJobExecutionNode execution |
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
  exists(MatrixJobExecutionNode execution, MatrixJobCompletionNode completion |
    predecessor = execution and
    completion.getInstance() = execution.getInstance() and
    successor = completion
  )
  or
  exists(MatrixJobCompletionNode completion, MatrixJobFanInNode fanIn |
    predecessor = completion and
    completion.getJob() = fanIn.getJob() and
    successor = fanIn
  )
  or
  exists(JobCompletionNode completion, WorkflowExitNode exit |
    predecessor = completion and
    isTerminalJob(completion.getJob()) and
    completion.getJob().getWorkflow() = exit.getWorkflow() and
    successor = exit
  )
  or
  exists(MatrixJobFanInNode fanIn, WorkflowExitNode exit |
    predecessor = fanIn and
    isTerminalJob(fanIn.getJob()) and
    fanIn.getJob().getWorkflow() = exit.getWorkflow() and
    successor = exit
  )
  or
  exists(WorkflowExitNode exit, JobCompletionNode completion |
    predecessor = exit and
    exit.getWorkflow() = getCalledReusableWorkflow(completion.getJob()) and
    not completion.getStatus() instanceof SkippedStatus and
    successor = completion
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
    needsStatusMayOccurForEvent(decision.getJob(), event, decision.getNeedsStatus()) and
    decisionMayHaveOutcome(decision.getJob(), event, decision.getNeedsStatus(), true) and
    successor = execution
  )
  or
  exists(JobDecisionNode decision, WorkflowEntryNode entry |
    predecessor = decision and
    entry.getWorkflow() = getCalledReusableWorkflow(decision.getJob()) and
    needsStatusMayOccurForEvent(decision.getJob(), event, decision.getNeedsStatus()) and
    decisionMayHaveOutcome(decision.getJob(), event, decision.getNeedsStatus(), true) and
    successor = entry
  )
  or
  exists(JobDecisionNode decision, JobCompletionNode completion |
    predecessor = decision and
    completion.getJob() = decision.getJob() and
    completion.getStatus() instanceof SkippedStatus and
    needsStatusMayOccurForEvent(decision.getJob(), event, decision.getNeedsStatus()) and
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
