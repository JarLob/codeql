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

bindingset[job, event, outcome]
pragma[inline_late]
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

bindingset[step, event, outcome]
pragma[inline_late]
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

private predicate stepAlwaysContinuesOnError(Step step) {
  step.getContinueOnErrorValue().toLowerCase() = "true"
  or
  getStaticContinueOnErrorValue(step.getContinueOnErrorExpr(), true)
}

private predicate jobAlwaysMasksStepFailures(Job job) {
  jobAlwaysContinuesOnError(job)
  or
  job instanceof LocalJob and
  exists(job.(LocalJob).getAContainedStep()) and
  forall(Step step | step = job.(LocalJob).getAContainedStep() |
    stepAlwaysContinuesOnError(step)
  )
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

bindingset[expression]
pragma[inline_late]
private string getMatrixAccessPath(Expression expression) {
  exists(MatrixAccessExpression access, string path |
    access.getExpression() = expression and
    path = access.getAccessPath() and
    result = path.suffix("matrix.".length())
  )
}

bindingset[job]
pragma[inline_late]
private string getSynchronizationMatrixAccessPath(Job job) {
  result = getMatrixAccessPath(job.getContinueOnErrorExpr())
  or
  exists(LocalJob local, Step step |
    local = job and
    step = local.getAContainedStep() and
    (
      result = getMatrixAccessPath(step.getContinueOnErrorExpr())
      or
      result = getMatrixAccessPath(step.getIf().getConditionExpr())
    )
  )
  or
  exists(ExternalJob caller |
    caller = job and result = getMatrixAccessPath(caller.getArgumentExpr(_))
  )
}

bindingset[job]
pragma[inline_late]
private string getSynchronizationMatrixDimension(Job job) {
  exists(string path |
    path = getSynchronizationMatrixAccessPath(job) and
    (
      exists(path.indexOf(".")) and result = path.prefix(path.indexOf("."))
      or
      not exists(path.indexOf(".")) and result = path
    )
  )
}

private string getMatrixDimensionAt(Job job, int index) {
  result =
    rank[index + 1](string dimension |
      dimension = job.getStrategy().getAMatrixDimensionName()
    |
      dimension order by dimension
    )
}

private string getProjectedBaseMatrixAssignmentPrefix(Job job, int length) {
  length = 0 and result = ""
  or
  exists(string prefix, string dimension |
    length > 0 and
    dimension = getMatrixDimensionAt(job, length - 1) and
    prefix = getProjectedBaseMatrixAssignmentPrefix(job, length - 1) and
    (
      dimension = getSynchronizationMatrixDimension(job) and
      exists(int valueIndex |
        valueIndex in [0 .. job.getStrategy().getMatrixDimensionValueCount(dimension) - 1] and
        (
          prefix = "" and result = dimension + "=" + valueIndex.toString()
          or
          prefix != "" and result = prefix + "," + dimension + "=" + valueIndex.toString()
        )
      )
      or
      not dimension = getSynchronizationMatrixDimension(job) and result = prefix
    )
  )
}

private string getAProjectedBaseMatrixAssignment(Job job) {
  job.getStrategy().hasStaticMatrixProjection() and
  job.getStrategy().hasPossibleProjectedBaseCombination() and
  result =
    getProjectedBaseMatrixAssignmentPrefix(job,
      count(job.getStrategy().getAMatrixDimensionName()))
}

private newtype TMatrixJobInstance =
  TProjectedMatrixJobInstance(Job job, string assignment) {
    exists(string baseAssignment |
      baseAssignment = getAProjectedBaseMatrixAssignment(job) and
      assignment = job.getStrategy().getAProjectedMatrixAssignment(baseAssignment) and
      (
        not exists(job.getStrategy().getAProjectedMatrixIncludeKey(assignment))
        or
        exists(string key |
          key = job.getStrategy().getAProjectedMatrixIncludeKey(assignment) and
          key = getSynchronizationMatrixDimension(job)
        )
      )
    )
    or
    assignment = job.getStrategy().getAProjectedMatrixIncludeAssignment() and
    (
      not exists(getAProjectedBaseMatrixAssignment(job))
      or
      exists(string key |
        key = job.getStrategy().getAProjectedMatrixIncludeKey(assignment) and
        key = getSynchronizationMatrixDimension(job)
      )
    )
  } or
  TWildcardMatrixJobInstance(Job job) {
    job.getStrategy().hasMatrix() and not job.getStrategy().hasStaticMatrixProjection()
  }

/** A demand-projected static expansion, or conservative wildcard expansion, of a matrix job. */
class MatrixJobInstance extends TMatrixJobInstance {
  Job getJob() {
    this = TProjectedMatrixJobInstance(result, _) or this = TWildcardMatrixJobInstance(result)
  }

  private string getProjectedAssignment() { this = TProjectedMatrixJobInstance(_, result) }

  string getAssignment() {
    exists(string assignment |
      assignment = this.getProjectedAssignment() and
      assignment.matches("base:%") and
      not exists(assignment.indexOf(":include=")) and
      result = assignment.suffix("base:".length()) and
      result != ""
    )
    or
    this.getProjectedAssignment() = "base:" and result = "*"
    or
    exists(string assignment |
      assignment = this.getProjectedAssignment() and
      (
        assignment.matches("include=%") or assignment.matches("base:%:include=%")
      ) and
      result = assignment
    )
    or
    this = TWildcardMatrixJobInstance(_) and result = "*"
  }

  string getAMatrixKey() {
    result = this.getJob().getStrategy().getAProjectedMatrixKey(this.getProjectedAssignment())
  }

  bindingset[name]
  pragma[inline_late]
  string getMatrixValue(string name) {
    result =
      this.getJob().getStrategy().getProjectedMatrixValue(this.getProjectedAssignment(), name)
  }

  bindingset[name]
  pragma[inline_late]
  string getMatrixValueKind(string name) {
    result =
      this.getJob().getStrategy().getProjectedMatrixValueKind(this.getProjectedAssignment(), name)
  }

  /** Gets a statically known output value from the reusable workflow called by this instance. */
  string getReusableWorkflowOutputValue(string name) {
    name = getCalledReusableWorkflow(this.getJob()).getOutputs().getAnOutputName() and
    result = getMatrixReusableWorkflowOutputStringValue(this, name)
  }

  string toString() { result = this.getJob().getId() + "[" + this.getAssignment() + "]" }
}

/**
 * Holds if `node` is a literal or an exactly known scalar for `instance`.
 *
 * Wildcard matrix instances deliberately yield no value here. Callers treat that absence as an
 * unknown expression result rather than choosing a value for the dynamic matrix.
 */
private predicate getMatrixInstanceScalarValue(
  ExpressionNode node, MatrixJobInstance instance, string kind, string value
) {
  node instanceof LiteralExpression and
  kind = node.getKind() and
  (
    kind = "StringLiteral" and value = getStringLiteralValue(node)
    or
    kind = ["BooleanLiteral", "NumberLiteral", "NullLiteral"] and
    value = node.(LiteralExpression).getValue()
  )
  or
  exists(AccessExpression access, string path, string accessPath |
    access = node and
    path = access.getAccessPath() and
    path.toLowerCase().matches("matrix.%") and
    accessPath = path.suffix("matrix.".length()) and
    kind = instance.getMatrixValueKind(accessPath) and
    value = instance.getMatrixValue(accessPath)
  )
}

private predicate matrixContinueOnErrorScalarEvaluatesTo(
  ExpressionNode node, MatrixJobInstance instance, boolean outcome
) {
  exists(string value |
    getMatrixInstanceScalarValue(node, instance, "BooleanLiteral", value) and
    value.toLowerCase() = outcome.toString()
  )
  or
  getMatrixInstanceScalarValue(node, instance, "NullLiteral", _) and outcome = false
  or
  exists(string value |
    getMatrixInstanceScalarValue(node, instance, "StringLiteral", value) and
    stringTruthinessEvaluatesTo(value, outcome)
  )
  or
  exists(string value, float number |
    getMatrixInstanceScalarValue(node, instance, "NumberLiteral", value) and
    number = value.toFloat() and
    numericTruthinessEvaluatesTo(number, outcome)
  )
}

private predicate matrixContinueOnErrorComparisonEvaluatesTo(
  BinaryExpression expression, MatrixJobInstance instance, boolean outcome
) {
  exists(string left, string right |
    getMatrixInstanceScalarValue(expression.getLeftOperand(), instance, "StringLiteral", left) and
    getMatrixInstanceScalarValue(expression.getRightOperand(), instance, "StringLiteral", right) and
    stringComparisonEvaluatesTo(left, expression.getOperator(), right, outcome)
  )
  or
  exists(string left, string right, boolean leftBoolean, boolean rightBoolean |
    getMatrixInstanceScalarValue(expression.getLeftOperand(), instance, "BooleanLiteral", left) and
    getMatrixInstanceScalarValue(expression.getRightOperand(), instance, "BooleanLiteral", right) and
    left.toLowerCase() = leftBoolean.toString() and
    right.toLowerCase() = rightBoolean.toString() and
    booleanComparisonEvaluatesTo(leftBoolean, expression.getOperator(), rightBoolean, outcome)
  )
  or
  exists(string left, string right, float leftNumber, float rightNumber |
    getMatrixInstanceScalarValue(expression.getLeftOperand(), instance, "NumberLiteral", left) and
    getMatrixInstanceScalarValue(expression.getRightOperand(), instance, "NumberLiteral", right) and
    leftNumber = left.toFloat() and
    rightNumber = right.toFloat() and
    numericComparisonEvaluatesTo(leftNumber, expression.getOperator(), rightNumber, outcome)
  )
  or
  getMatrixInstanceScalarValue(expression.getLeftOperand(), instance, "NullLiteral", _) and
  getMatrixInstanceScalarValue(expression.getRightOperand(), instance, "NullLiteral", _) and
  nullComparisonEvaluatesTo(expression.getOperator(), outcome)
}

private predicate matrixContinueOnErrorLevel0EvaluatesTo(
  ExpressionNode node, MatrixJobInstance instance, boolean outcome
) {
  matrixContinueOnErrorScalarEvaluatesTo(node, instance, outcome)
  or
  node instanceof BinaryExpression and
  node.(BinaryExpression).getOperator() = ["==", "!=", ">", ">=", "<", "<="] and
  matrixContinueOnErrorComparisonEvaluatesTo(node.(BinaryExpression), instance, outcome)
}

private predicate matrixContinueOnErrorLevel0OperandEvaluatesTo(
  BinaryExpression expression, int index, MatrixJobInstance instance, boolean outcome
) {
  index = 0 and
  matrixContinueOnErrorLevel0EvaluatesTo(expression.getLeftOperand(), instance, outcome)
  or
  index = 1 and
  matrixContinueOnErrorLevel0EvaluatesTo(expression.getRightOperand(), instance, outcome)
}

/**
 * Holds if one bounded logical layer evaluates to `outcome` for `instance`.
 *
 * The bound avoids joining synchronization against the recursive public matrix evaluator.
 * Deeper or unsupported expressions yield no result here, allowing callers to retain both outcomes.
 */
private predicate matrixContinueOnErrorLevel1EvaluatesTo(
  ExpressionNode node, MatrixJobInstance instance, boolean outcome
) {
  matrixContinueOnErrorLevel0EvaluatesTo(node, instance, outcome)
  or
  node instanceof UnaryExpression and
  node.(UnaryExpression).getOperator() = "!" and
  exists(boolean operandOutcome |
    matrixContinueOnErrorLevel0EvaluatesTo(
      node.(UnaryExpression).getOperand(), instance, operandOutcome
    ) and
    (
      operandOutcome = true and outcome = false
      or
      operandOutcome = false and outcome = true
    )
  )
  or
  node instanceof BinaryExpression and
  (
    node.(BinaryExpression).getOperator() = "&&" and
    outcome = false and
    matrixContinueOnErrorLevel0OperandEvaluatesTo(node.(BinaryExpression), _, instance, false)
    or
    node.(BinaryExpression).getOperator() = "&&" and
    outcome = true and
    matrixContinueOnErrorLevel0OperandEvaluatesTo(node.(BinaryExpression), 0, instance, true) and
    matrixContinueOnErrorLevel0OperandEvaluatesTo(node.(BinaryExpression), 1, instance, true)
    or
    node.(BinaryExpression).getOperator() = "||" and
    outcome = true and
    matrixContinueOnErrorLevel0OperandEvaluatesTo(node.(BinaryExpression), _, instance, true)
    or
    node.(BinaryExpression).getOperator() = "||" and
    outcome = false and
    matrixContinueOnErrorLevel0OperandEvaluatesTo(node.(BinaryExpression), 0, instance, false) and
    matrixContinueOnErrorLevel0OperandEvaluatesTo(node.(BinaryExpression), 1, instance, false)
  )
}

private predicate getInstanceContinueOnErrorValue(
  Expression expression, MatrixJobInstance instance, Event event, boolean outcome
) {
  (
    expression.getATriggerEvent() = event
    or
    not exists(expression.getATriggerEvent())
  ) and
  matrixContinueOnErrorLevel1EvaluatesTo(expression.getRoot().getChild(0), instance, outcome)
}

private predicate jobHasDynamicContinueOnError(Job job) {
  exists(string value |
    value = job.getContinueOnErrorValue() and
    not value.toLowerCase() = ["true", "false"]
  )
}

private predicate stepHasDynamicContinueOnError(Step step) {
  exists(string value |
    value = step.getContinueOnErrorValue() and
    not value.toLowerCase() = ["true", "false"]
  )
}

/**
 * Holds if the job-level `continue-on-error` may evaluate to `outcome` for `instance`.
 *
 * If the bounded evaluator establishes neither Boolean value, both outcomes are retained. This
 * covers wildcard matrices and unsupported expressions without suppressing a feasible conclusion.
 */
private predicate matrixJobContinueOnErrorMayEvaluateTo(
  MatrixJobInstance instance, Event event, boolean outcome
) {
  instance.getJob().getATriggerEvent() = event and
  jobHasDynamicContinueOnError(instance.getJob()) and
  (
    getInstanceContinueOnErrorValue(instance.getJob().getContinueOnErrorExpr(), instance, event,
      outcome)
    or
    not exists(boolean known |
      getInstanceContinueOnErrorValue(instance.getJob().getContinueOnErrorExpr(), instance, event,
        known)
    ) and
    outcome in [false, true]
  )
}

/**
 * Holds if the step-level `continue-on-error` may evaluate to `outcome` for `instance`.
 *
 * As for job-level evaluation, an unresolved expression retains both outcomes so synchronization
 * does not assume that a dynamically configured step either always or never masks a failure.
 */
private predicate matrixStepContinueOnErrorMayEvaluateTo(
  Step step, MatrixJobInstance instance, Event event, boolean outcome
) {
  step.getEnclosingJob() = instance.getJob() and
  step.getATriggerEvent() = event and
  stepHasDynamicContinueOnError(step) and
  (
    getInstanceContinueOnErrorValue(step.getContinueOnErrorExpr(), instance, event, outcome)
    or
    not exists(boolean known |
      getInstanceContinueOnErrorValue(step.getContinueOnErrorExpr(), instance, event, known)
    ) and
    outcome in [false, true]
  )
}

private predicate matrixJobAlwaysMasksStepFailures(MatrixJobInstance instance) {
  not jobHasDynamicContinueOnError(instance.getJob()) and
  jobAlwaysContinuesOnError(instance.getJob())
  or
  jobHasDynamicContinueOnError(instance.getJob()) and
  exists(Event event |
    instance.getJob().getATriggerEvent() = event and
    matrixJobContinueOnErrorMayEvaluateTo(instance, event, true) and
    not matrixJobContinueOnErrorMayEvaluateTo(instance, event, false)
  )
  or
  instance.getJob() instanceof LocalJob and
  exists(instance.getJob().(LocalJob).getAContainedStep()) and
  forall(Step step | step = instance.getJob().(LocalJob).getAContainedStep() |
    not stepHasDynamicContinueOnError(step) and stepAlwaysContinuesOnError(step)
    or
    stepHasDynamicContinueOnError(step) and
    exists(Event event |
      step.getATriggerEvent() = event and
      matrixStepContinueOnErrorMayEvaluateTo(step, instance, event, true) and
      not matrixStepContinueOnErrorMayEvaluateTo(step, instance, event, false)
    )
  )
}

private predicate allMatrixInstancesAlwaysMaskStepFailures(Job job) {
  exists(MatrixJobInstance instance | instance.getJob() = job) and
  forall(MatrixJobInstance instance | instance.getJob() = job |
    matrixJobAlwaysMasksStepFailures(instance)
  )
}

/** Gets a possible effective conclusion for a matrix instance's raw outcome. */
bindingset[instance, event, outcome]
JobStatus getAMatrixJobConclusionForOutcome(
  MatrixJobInstance instance, Event event, JobStatus outcome
) {
  not outcome instanceof FailureStatus and result = outcome
  or
  outcome instanceof FailureStatus and
  not jobHasDynamicContinueOnError(instance.getJob()) and
  not jobAlwaysContinuesOnError(instance.getJob()) and
  result instanceof FailureStatus
  or
  outcome instanceof FailureStatus and
  not jobHasDynamicContinueOnError(instance.getJob()) and
  jobAlwaysContinuesOnError(instance.getJob()) and
  result instanceof SuccessStatus
  or
  outcome instanceof FailureStatus and
  jobHasDynamicContinueOnError(instance.getJob()) and
  matrixJobContinueOnErrorMayEvaluateTo(instance, event, false) and
  result instanceof FailureStatus
  or
  outcome instanceof FailureStatus and
  jobHasDynamicContinueOnError(instance.getJob()) and
  matrixJobContinueOnErrorMayEvaluateTo(instance, event, true) and
  result instanceof SuccessStatus
}

/** Gets a possible effective conclusion for a step's raw outcome in a matrix instance. */
bindingset[step, instance, event, outcome]
JobStatus getAMatrixStepConclusionForOutcome(
  Step step, MatrixJobInstance instance, Event event, JobStatus outcome
) {
  not outcome instanceof FailureStatus and result = outcome
  or
  outcome instanceof FailureStatus and
  not stepHasDynamicContinueOnError(step) and
  not stepAlwaysContinuesOnError(step) and
  result instanceof FailureStatus
  or
  outcome instanceof FailureStatus and
  not stepHasDynamicContinueOnError(step) and
  stepAlwaysContinuesOnError(step) and
  result instanceof SuccessStatus
  or
  outcome instanceof FailureStatus and
  stepHasDynamicContinueOnError(step) and
  matrixStepContinueOnErrorMayEvaluateTo(step, instance, event, false) and
  result instanceof FailureStatus
  or
  outcome instanceof FailureStatus and
  stepHasDynamicContinueOnError(step) and
  matrixStepContinueOnErrorMayEvaluateTo(step, instance, event, true) and
  result instanceof SuccessStatus
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
    not (status instanceof FailureStatus and jobAlwaysMasksStepFailures(job)) and
    (not status instanceof SkippedStatus or jobMayBeSkipped(job))
  } or
  TMatrixJobExecutionNode(MatrixJobInstance instance) or
  TMatrixJobCompletionNode(MatrixJobInstance instance, JobStatus status) {
    not status instanceof SkippedStatus and
    not (status instanceof FailureStatus and matrixJobAlwaysMasksStepFailures(instance))
  } or
  TMatrixJobFanInNode(Job job, JobStatus status) {
    job.getStrategy().hasMatrix() and
    not status instanceof SkippedStatus and
    not (status instanceof FailureStatus and allMatrixInstancesAlwaysMaskStepFailures(job))
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

  /** Gets a raw job outcome that may produce this effective conclusion for `event`. */
  JobStatus getAOutcome(Event event) {
    this.getJob().getATriggerEvent() = event and
    this.getStatus() = getAJobConclusionForOutcome(this.getJob(), event, result)
  }

  /** Gets a raw step outcome that may contribute to this effective job conclusion. */
  JobStatus getAContributingStepOutcome(Step step, Event event) {
    step.getEnclosingJob() = this.getJob() and
    exists(JobStatus stepConclusion |
      stepConclusion = getAStepConclusionForOutcome(step, event, result) and
      this.getStatus() = getAJobConclusionForOutcome(this.getJob(), event, stepConclusion)
    )
  }

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

  /** Gets a raw instance outcome that may produce this effective conclusion for `event`. */
  JobStatus getAOutcome(Event event) {
    this.getJob().getATriggerEvent() = event and
    this.getStatus() = getAMatrixJobConclusionForOutcome(this.getInstance(), event, result)
  }

  /** Gets a raw step outcome that may contribute to this effective instance conclusion. */
  JobStatus getAContributingStepOutcome(Step step, Event event) {
    step.getEnclosingJob() = this.getJob() and
    exists(JobStatus stepConclusion |
      stepConclusion =
        getAMatrixStepConclusionForOutcome(step, this.getInstance(), event, result) and
      this.getStatus() =
        getAMatrixJobConclusionForOutcome(this.getInstance(), event, stepConclusion)
    )
  }

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

private JobStatus getAPossibleNonMatrixJobConclusionForEvent(Job job, Event event) {
  not job.getStrategy().hasMatrix() and
  job.getATriggerEvent() = event and
  (
    exists(LocalJob local, Step step, JobStatus outcome, JobStatus stepConclusion |
      local = job and
      step = local.getAContainedStep() and
      not outcome instanceof SkippedStatus and
      stepConclusion = getAStepConclusionForOutcome(step, event, outcome) and
      result = getAJobConclusionForOutcome(job, event, stepConclusion)
    )
    or
    not exists(LocalJob local, Step step | local = job and step = local.getAContainedStep()) and
    exists(JobStatus outcome |
      not outcome instanceof SkippedStatus and
      result = getAJobConclusionForOutcome(job, event, outcome)
    )
  )
}

private JobStatus getAPossibleMatrixInstanceConclusionForEvent(
  MatrixJobInstance instance, Event event
) {
  instance.getJob().getATriggerEvent() = event and
  (
    exists(LocalJob local, Step step, JobStatus outcome, JobStatus stepConclusion |
      local = instance.getJob() and
      step = local.getAContainedStep() and
      not outcome instanceof SkippedStatus and
      stepConclusion = getAMatrixStepConclusionForOutcome(step, instance, event, outcome) and
      result = getAMatrixJobConclusionForOutcome(instance, event, stepConclusion)
    )
    or
    not exists(LocalJob local, Step step |
      local = instance.getJob() and step = local.getAContainedStep()
    ) and
    exists(JobStatus outcome |
      not outcome instanceof SkippedStatus and
      result = getAMatrixJobConclusionForOutcome(instance, event, outcome)
    )
  )
}

private JobStatus getAPossibleMatrixJobConclusionForEvent(Job job, Event event) {
  job.getStrategy().hasMatrix() and
  job.getATriggerEvent() = event and
  exists(MatrixJobFanInNode fanIn |
    fanIn.getJob() = job and
    fanIn.getStatus() = result and
    (
      result instanceof FailureStatus and
      exists(MatrixJobInstance instance |
        instance.getJob() = job and
        getAPossibleMatrixInstanceConclusionForEvent(instance, event) = result
      )
      or
      result instanceof CancelledStatus and
      exists(MatrixJobInstance instance |
        instance.getJob() = job and
        getAPossibleMatrixInstanceConclusionForEvent(instance, event) = result
      ) and
      forall(MatrixJobInstance instance | instance.getJob() = job |
        exists(JobStatus conclusion |
          conclusion = getAPossibleMatrixInstanceConclusionForEvent(instance, event) and
          not conclusion instanceof FailureStatus
        )
      )
      or
      result instanceof SuccessStatus and
      forall(MatrixJobInstance instance | instance.getJob() = job |
        getAPossibleMatrixInstanceConclusionForEvent(instance, event) = result
      )
    )
  )
}

private JobStatus getAPossibleNonReusableJobConclusionForEvent(Job job, Event event) {
  not exists(getCalledReusableWorkflow(job)) and
  (
    result = getAPossibleNonMatrixJobConclusionForEvent(job, event)
    or
    result = getAPossibleMatrixJobConclusionForEvent(job, event)
  )
}

private predicate isTerminalJob(Job job) {
  not exists(Job dependent | dependent.getANeededJob() = job)
}

private predicate structuralTerminalJobMayComplete(Job terminal, JobStatus status) {
  exists(JobCompletionNode completion |
    completion.getJob() = terminal and completion.getStatus() = status
  )
  or
  exists(MatrixJobFanInNode fanIn | fanIn.getJob() = terminal and fanIn.getStatus() = status)
}

private predicate terminalJobMayCompleteForEvent(
  Job terminal, Event event, JobStatus status
) {
  exists(ReusableWorkflow workflow, JobStatus outcome |
    workflow = getCalledReusableWorkflow(terminal) and
    terminal.getATriggerEvent() = event and
    reusableWorkflowMayCompleteForEvent(workflow, event, outcome) and
    status = getAJobConclusionForOutcome(terminal, event, outcome)
  )
  or
  not exists(getCalledReusableWorkflow(terminal)) and
  terminal.getATriggerEvent() = event and
  (
    isRootJob(terminal) and
    not terminal.getStrategy().hasMatrix() and
    (
      status instanceof SkippedStatus and ownConditionMayHaveOutcome(terminal, event, false)
      or
      not status instanceof SkippedStatus and
      ownConditionMayHaveOutcome(terminal, event, true) and
      status = getAPossibleNonReusableJobConclusionForEvent(terminal, event)
    )
    or
    (not isRootJob(terminal) or terminal.getStrategy().hasMatrix()) and
    structuralTerminalJobMayComplete(terminal, status)
  )
}

private predicate reusableWorkflowMayCompleteForEvent(
  ReusableWorkflow workflow, Event event, JobStatus status
) {
  status instanceof FailureStatus and
  exists(Job terminal |
    terminal.getWorkflow() = workflow and
    isTerminalJob(terminal) and
    terminalJobMayCompleteForEvent(terminal, event, status)
  )
  or
  status instanceof CancelledStatus and
  exists(Job terminal |
    terminal.getWorkflow() = workflow and
    isTerminalJob(terminal) and
    terminalJobMayCompleteForEvent(terminal, event, status)
  )
  or
  status instanceof SuccessStatus and
  not exists(Job terminal |
    terminal.getWorkflow() = workflow and
    isTerminalJob(terminal) and
    not exists(JobStatus terminalStatus |
      terminalJobMayCompleteForEvent(terminal, event, terminalStatus) and
      (terminalStatus instanceof SuccessStatus or terminalStatus instanceof SkippedStatus)
    )
  )
}

private JobStatus getAPossibleExecutedJobConclusionForEvent(Job job, Event event) {
  exists(ReusableWorkflow workflow, JobStatus outcome |
    workflow = getCalledReusableWorkflow(job) and
    reusableWorkflowMayCompleteForEvent(workflow, event, outcome) and
    result = getAJobConclusionForOutcome(job, event, outcome)
  )
  or
  result = getAPossibleNonReusableJobConclusionForEvent(job, event)
}

/**
 * Holds if a reusable-workflow matrix invocation may complete with `status` for `event`.
 *
 * Callee completion is not specialized by the caller's per-instance inputs, so every callee status
 * feasible for the event is retained for each instance. The caller's `continue-on-error` is still
 * applied per instance.
 */
private predicate reusableMatrixInstanceMayCompleteForEvent(
  MatrixJobInstance instance, Event event, JobStatus status
) {
  exists(ReusableWorkflow workflow, JobStatus outcome |
    workflow = getCalledReusableWorkflow(instance.getJob()) and
    instance.getJob().getATriggerEvent() = event and
    reusableWorkflowMayCompleteForEvent(workflow, event, outcome) and
    status = getAMatrixJobConclusionForOutcome(instance, event, outcome)
  )
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
  jobConditionUsesExactNeedsAssignment(job) and
  exists(string assignment |
    assignment = getANeededStatusAssignment(job, event) and
    getAssignmentSummary(assignment) = needsStatus and
    decisionMayHaveOutcomeForAssignment(job, event, assignment, outcome)
  )
  or
  not isRootJob(job) and
  jobConditionUsesSeparableNeedsAssignment(job) and
  separableConditionMayHaveOutcome(job, event, needsStatus, outcome)
  or
  not jobConditionUsesExactNeedsAssignment(job) and
  not jobConditionUsesSeparableNeedsAssignment(job) and
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
          needsStatus.hasCancellation(), needsStatus.hasSkip(), outcome) and
        mayEvaluateForNeedsStatus(condition.getConditionExpr().getRoot(), job, needsStatus, outcome)
        or
        exists(condition.getConditionExpr().getRoot()) and
        not hasStatusCheckFunction(condition) and
        (
          needsStatus.isSuccess() and
          mayEvaluateConditionToBoolean(condition, condition.getConditionExpr().getRoot(), event,
            outcome) and
          mayEvaluateForNeedsStatus(condition.getConditionExpr().getRoot(), job, needsStatus,
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

bindingset[summary, status]
private NeedsStatus addStatusToSummary(NeedsStatus summary, JobStatus status) {
  status instanceof SuccessStatus and result = summary
  or
  status instanceof FailureStatus and
  result = TNeedsStatusSummary(true, summary.hasCancellation(), summary.hasSkip())
  or
  status instanceof CancelledStatus and
  result = TNeedsStatusSummary(summary.hasFailure(), true, summary.hasSkip())
  or
  status instanceof SkippedStatus and
  result = TNeedsStatusSummary(summary.hasFailure(), summary.hasCancellation(), true)
}

/** Each prefix has at most the eight values in the three-bit `NeedsStatus` domain. */
private NeedsStatus getAReachableNeedsStatusPrefix(Job job, Event event, int length) {
  length = 0 and result = TNeedsStatusSummary(false, false, false)
  or
  exists(NeedsStatus prefix, Job needed, JobStatus status |
    length > 0 and
    needed = getNeededJobAt(job, length - 1) and
    prefix = getAReachableNeedsStatusPrefix(job, event, length - 1) and
    jobMayCompleteForEvent(needed, event, status) and
    result = addStatusToSummary(prefix, status)
  )
}

private NeedsStatus getAReachableNeedsStatus(Job job, Event event) {
  result = getAReachableNeedsStatusPrefix(job, event, count(job.getANeededJob()))
}

private NeedsStatus getAConservativeNeedsStatusForDirectStatus(
  Job job, Job directNeeded, JobStatus directStatus
) {
  directNeeded = job.getANeededJob() and
  (
    count(job.getANeededJob()) = 1 and
    result = addStatusToSummary(TNeedsStatusSummary(false, false, false), directStatus)
    or
    count(job.getANeededJob()) > 1 and
    (
      directStatus instanceof SuccessStatus
      or
      directStatus instanceof FailureStatus and result.hasFailure() = true
      or
      directStatus instanceof CancelledStatus and result.hasCancellation() = true
      or
      directStatus instanceof SkippedStatus and result.hasSkip() = true
    )
  )
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
    needed = getDemandedNeededJobAt(job, index) and
    result = getStatusForCode(assignment.charAt(index))
  )
}

private Job getDemandedNeededJobAt(Job job, int index) {
  result =
    rank[index + 1](Job needed |
      needed = getAConditionDemandedNeededJob(job)
    |
      needed order by needed.getId()
    )
}

private predicate getAReachableDemandedNeedsStatePrefix(
  Job job, Event event, int length, string assignment, NeedsStatus status
) {
  jobConditionUsesExactNeedsAssignment(job) and
  (
    length = 0 and
    assignment = "" and
    status = TNeedsStatusSummary(false, false, false)
    or
    exists(string prefixAssignment, NeedsStatus prefixStatus, Job needed, JobStatus neededStatus |
      length > 0 and
      needed = getNeededJobAt(job, length - 1) and
      getAReachableDemandedNeedsStatePrefix(job, event, length - 1, prefixAssignment,
        prefixStatus) and
      jobMayCompleteForEvent(needed, event, neededStatus) and
      status = addStatusToSummary(prefixStatus, neededStatus) and
      (
        needed = getAConditionDemandedNeededJob(job) and
        assignment = prefixAssignment + getStatusCode(neededStatus)
        or
        not needed = getAConditionDemandedNeededJob(job) and
        assignment = prefixAssignment
      )
    )
  )
}

private string getANeededStatusAssignment(Job job, Event event) {
  exists(string assignment, NeedsStatus status |
    getAReachableDemandedNeedsStatePrefix(job, event, count(job.getANeededJob()), assignment,
      status) and
    demandedNeedsAssignmentIsConsistent(job, assignment) and
    result = assignment + ":" + status.getName()
  )
}

bindingset[assignment]
private NeedsStatus getAssignmentSummary(string assignment) {
  result.getName() = assignment.splitAt(":", 1)
}

private predicate needsStatusMayOccurForEvent(Job job, Event event, NeedsStatus status) {
  jobConditionUsesExactNeedsAssignment(job) and
  exists(string assignment |
    assignment = getANeededStatusAssignment(job, event) and
    status = getAssignmentSummary(assignment)
  )
  or
  jobConditionUsesSeparableNeedsAssignment(job) and
  job.getATriggerEvent() = event and
  needsStatusMayOccur(job, status)
  or
  not jobConditionUsesExactNeedsAssignment(job) and
  not jobConditionUsesSeparableNeedsAssignment(job) and
  job.getATriggerEvent() = event and
  status = getAReachableNeedsStatus(job, event)
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

bindingset[expression, instance]
pragma[inline_late]
private string getMatrixInstanceExpressionStringValue(
  Expression expression, MatrixJobInstance instance
) {
  result = getStaticExpressionOutputStringValue(expression)
  or
  exists(AccessExpression access, string path, string accessPath |
    access = expression.getRoot().getChild(0) and
    path = access.getAccessPath() and
    path.toLowerCase().matches("matrix.%") and
    accessPath = path.suffix("matrix.".length()) and
    result = instance.getMatrixValue(accessPath)
  )
}

bindingset[instance, inputName]
pragma[inline_late]
private string getMatrixReusableWorkflowInputStringValue(
  MatrixJobInstance instance, string inputName
) {
  exists(ExternalJob caller, ReusableWorkflow workflow |
    caller = instance.getJob() and
    workflow = getCalledReusableWorkflow(caller) and
    inputName = workflow.getAnInput().toString() and
    result = getMatrixInstanceExpressionStringValue(caller.getArgumentExpr(inputName), instance)
  )
}

bindingset[instance, outputJob, outputName]
pragma[inline_late]
private string getMatrixReusableJobOutputStringValue(
  MatrixJobInstance instance, Job outputJob, string outputName
) {
  outputName = outputJob.getOutputs().getAnOutputName() and
  (
    result = getStaticExpressionOutputStringValue(outputJob.getOutputExpr(outputName))
    or
    exists(AccessExpression access, string inputName |
      access = outputJob.getOutputExpr(outputName).getRoot().getChild(0) and
      inputName = getCalledReusableWorkflow(instance.getJob()).getAnInput().toString() and
      access.getAccessPath().toLowerCase() = ("inputs." + inputName).toLowerCase() and
      result = getMatrixReusableWorkflowInputStringValue(instance, inputName)
    )
  )
}

bindingset[instance, outputName]
pragma[inline_late]
private string getMatrixReusableWorkflowOutputStringValue(
  MatrixJobInstance instance, string outputName
) {
  exists(ReusableWorkflow workflow |
    workflow = getCalledReusableWorkflow(instance.getJob()) and
    outputName = workflow.getOutputs().getAnOutputName() and
    (
      result = getStaticExpressionOutputStringValue(workflow.getOutputExpr(outputName))
      or
      exists(AccessExpression access, Job outputJob, string jobOutputName |
        access = workflow.getOutputExpr(outputName).getRoot().getChild(0) and
        jobOutputName = outputJob.getOutputs().getAnOutputName() and
        access.getAccessPath().toLowerCase() =
          ("jobs." + outputJob.getId() + ".outputs." + jobOutputName).toLowerCase() and
        outputJob.getWorkflow() = workflow and
        result = getMatrixReusableJobOutputStringValue(instance, outputJob, jobOutputName)
      )
    )
  )
}

private string getStaticOutputStringValue(Job needed, string outputName) {
  result = getStaticExpressionOutputStringValue(needed.getOutputExpr(outputName))
  or
  not exists(needed.getOutputExpr(outputName)) and
  result = needed.getOutputs().getOutputValue(outputName)
  or
  exists(ReusableWorkflow workflow |
    needed = workflow.getACaller() and
    result = getStaticExpressionOutputStringValue(workflow.getOutputExpr(outputName))
  )
  or
  exists(ReusableWorkflow workflow, AccessExpression access, Job outputJob, string jobOutputName |
    needed = workflow.getACaller() and
    access = workflow.getOutputExpr(outputName).getRoot().getChild(0) and
    access.getAccessPath().toLowerCase() =
      ("jobs." + outputJob.getId() + ".outputs." + jobOutputName).toLowerCase() and
    outputJob.getWorkflow() = workflow and
    result = getStaticOutputStringValue(outputJob, jobOutputName)
  )
  or
  exists(MatrixJobInstance instance, ReusableWorkflow workflow |
    instance.getJob() = needed and
    workflow = getCalledReusableWorkflow(needed) and
    outputName = workflow.getOutputs().getAnOutputName() and
    result = getMatrixReusableWorkflowOutputStringValue(instance, outputName)
  )
}

bindingset[needed]
private string getANeededOutputName(Job needed) {
  result = needed.getOutputs().getAnOutputName()
  or
  exists(ReusableWorkflow workflow |
    needed = workflow.getACaller() and result = workflow.getOutputs().getAnOutputName()
  )
}

bindingset[access, needed, outputName]
private predicate accessesNeededOutput(AccessExpression access, Job needed, string outputName) {
  access.getAccessPath().toLowerCase() =
    ("needs." + needed.getId() + ".outputs." + outputName).toLowerCase()
  or
  access.getAccessPath().toLowerCase() =
    ("needs." + needed.getId() + ".outputs['" + outputName + "']").toLowerCase()
}

bindingset[node, job]
private string getReferencedStaticOutputStringValue(ExpressionNode node, Job job, Job needed) {
  exists(AccessExpression access, string outputName |
    access = node and
    needed = job.getANeededJob() and
    outputName = getANeededOutputName(needed) and
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

bindingset[node, job, status]
private string getSummaryStringValue(ExpressionNode node, Job job, NeedsStatus status) {
  result = getStringLiteralValue(node)
  or
  exists(Job needed, string staticValue |
    staticValue = getReferencedStaticOutputStringValue(node, job, needed) and
    (
      status.isSuccess() and result = staticValue
      or
      not status.isSuccess() and result = [staticValue, ""]
    )
  )
}

bindingset[access, job]
pragma[inline_late]
private Job getReferencedNeededResult(AccessExpression access, Job job) {
  result = job.getANeededJob() and
  access.getAccessPath() = "needs." + result.getId() + ".result"
}

private predicate jobConditionContainsAssignedNeedsValue(Job job) {
  exists(If condition, ExpressionNode node, Job needed |
    condition = job.getIf() and
    node.getExpression() = condition.getConditionExpr() and
    needed = job.getANeededJob() and
    (
      node instanceof AccessExpression and
      node.(AccessExpression).getAccessPath() = "needs." + needed.getId() + ".result"
      or
      exists(getReferencedStaticOutputStringValue(node, job, needed))
    )
  )
}

/** Holds if assignment evaluation directly reads the scalar value of `access`. */
private predicate isDirectlyEvaluatedAssignedNeedsValue(AccessExpression access) {
  access.getParent() instanceof ExpressionRoot
  or
  access.getParent() instanceof UnaryExpression
  or
  exists(BinaryExpression parent |
    parent = access.getParent() and parent.getOperator() = ["&&", "||", "==", "!="]
  )
}

private Job getAConditionReferencedNeededJob(Job job) {
  exists(If condition, AccessExpression access |
    condition = job.getIf() and
    access.getExpression() = condition.getConditionExpr() and
    isDirectlyEvaluatedAssignedNeedsValue(access) and
    result = getReferencedNeededResult(access, job)
  )
}

private predicate jobConditionUsesAggregateNeedsStatus(Job job) {
  exists(If condition, FunctionCallExpression call |
    condition = job.getIf() and
    call.getExpression() = condition.getConditionExpr() and
    call.getCallee().getName().toLowerCase() = ["cancelled", "failure", "success"]
  )
}

private Job getAConditionDemandedNeededJob(Job job) {
  result = getAConditionReferencedNeededJob(job)
  or
  exists(Job referenced |
    jobConditionUsesAggregateNeedsStatus(job) and
    referenced = getAConditionReferencedNeededJob(job) and
    result = job.getANeededJob() and
    result = referenced.getANeededJob+()
  )
}

private predicate structurallyRequiresSuccessfulCompletionOf(Job job, Job prerequisite) {
  prerequisite = job.getANeededJob() and not jobConditionHasStatusCheckFunction(job)
  or
  exists(Job directPrerequisite |
    directPrerequisite = job.getANeededJob() and
    not jobConditionHasStatusCheckFunction(job) and
    structurallyRequiresSuccessfulCompletionOf(directPrerequisite, prerequisite)
  )
}

bindingset[job, assignment]
pragma[inline_late]
private predicate demandedNeedsAssignmentIsConsistent(Job job, string assignment) {
  forall(Job dependent, Job prerequisite |
    dependent = getAConditionDemandedNeededJob(job) and
    prerequisite = getAConditionDemandedNeededJob(job) and
    structurallyRequiresSuccessfulCompletionOf(dependent, prerequisite)
  |
    getAssignedStatus(job, assignment, dependent) instanceof SkippedStatus
    or
    getAssignedStatus(job, assignment, prerequisite) instanceof SuccessStatus
  )
}

private Job getASeparableComparisonNeededJob(BinaryExpression comparison, Job job) {
  comparison.getOperator() = ["==", "!="] and
  exists(AccessExpression access |
    access.getParent() = comparison and
    result = getReferencedNeededResult(access, job)
  )
}

private predicate isLogicallyComposedNeedsComparison(BinaryExpression comparison) {
  forall(ExpressionNode ancestor | ancestor = comparison.getParent+() |
    ancestor instanceof ExpressionRoot
    or
    ancestor instanceof UnaryExpression
    or
    ancestor instanceof BinaryExpression and
    ancestor.(BinaryExpression).getOperator() = ["&&", "||"]
  )
}

private predicate jobConditionUsesSeparableNeedsAssignment(Job job) {
  exists(getAConditionDemandedNeededJob(job)) and
  forall(AccessExpression access, Job needed |
    access.getExpression() = job.getIf().getConditionExpr() and
    isDirectlyEvaluatedAssignedNeedsValue(access) and
    needed = getReferencedNeededResult(access, job)
  |
    exists(BinaryExpression comparison |
      comparison = access.getParent() and
      isLogicallyComposedNeedsComparison(comparison) and
      count(getASeparableComparisonNeededJob(comparison, job)) = 1
    )
  )
}

private predicate jobConditionUsesExactNeedsAssignment(Job job) {
  exists(getAConditionDemandedNeededJob(job)) and
  not jobConditionUsesSeparableNeedsAssignment(job)
}

bindingset[job]
pragma[inline_late]
private string getUnknownDirectNeedsAssignment(Job job) {
  result =
    concat(int index | index in [0 .. count(job.getANeededJob()) - 1] |
      "?", "" order by index
    )
}

bindingset[job, needed, status]
pragma[inline_late]
private string getSingleStatusPartialAssignment(Job job, Job needed, JobStatus status) {
  needed = job.getANeededJob() and
  result =
    concat(int index, string code |
      index in [0 .. count(job.getANeededJob()) - 1] and
      (
        getNeededJobAt(job, index) = needed and code = getStatusCode(status)
        or
        not getNeededJobAt(job, index) = needed and code = "?"
      )
    |
      code, "" order by index
    )
}

bindingset[job, left, right]
pragma[inline_late]
private string mergePartialAssignments(Job job, string left, string right) {
  left.length() = count(job.getANeededJob()) and
  right.length() = left.length() and
  result =
    concat(int index, string code |
      index in [0 .. left.length() - 1] and
      (
        left.charAt(index) = "?" and code = right.charAt(index)
        or
        right.charAt(index) = "?" and code = left.charAt(index)
        or
        left.charAt(index) = right.charAt(index) and code = left.charAt(index)
      )
    |
      code, "" order by index
    ) and
  result.length() = left.length()
}

bindingset[job, assignment, needed]
pragma[inline_late]
private JobStatus getPartialAssignedStatus(Job job, string assignment, Job needed) {
  exists(int index |
    needed = getNeededJobAt(job, index) and
    result = getStatusForCode(assignment.charAt(index))
  )
}

bindingset[node, job, assignment]
pragma[inline_late]
private string getPartialAssignedStringValue(
  ExpressionNode node, Job job, string assignment
) {
  result = getStringLiteralValue(node)
  or
  exists(AccessExpression access, Job needed |
    access = node and
    needed = getReferencedNeededResult(access, job) and
    result = getPartialAssignedStatus(job, assignment, needed).getName()
  )
  or
  exists(Job needed, JobStatus status, string staticValue |
    staticValue = getReferencedStaticOutputStringValue(node, job, needed) and
    status = getPartialAssignedStatus(job, assignment, needed) and
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

bindingset[node, job]
pragma[inline_late]
private predicate containsDirectlyEvaluatedNeededResult(ExpressionNode node, Job job) {
  exists(AccessExpression access |
    (access = node or access.getParent+() = node) and
    isDirectlyEvaluatedAssignedNeedsValue(access) and
    exists(getReferencedNeededResult(access, job))
  )
}

private predicate directNeededStatusMayOccurForEvent(
  Job needed, Event event, JobStatus status
) {
  needed.getATriggerEvent() = event and
  (
    status instanceof SkippedStatus and jobMayBeSkipped(needed)
    or
    not status instanceof SkippedStatus and
    status = getAPossibleExecutedJobConclusionForEvent(needed, event)
  )
}

private predicate separableComparisonMayEvaluateTo(
  BinaryExpression comparison, Job job, Event event, string assignment, boolean outcome
) {
  exists(Job needed, JobStatus status |
    needed = getASeparableComparisonNeededJob(comparison, job) and
    directNeededStatusMayOccurForEvent(needed, event, status) and
    assignment = getSingleStatusPartialAssignment(job, needed, status) and
    (
      stringComparisonEvaluatesTo(
        getPartialAssignedStringValue(comparison.getLeftOperand(), job, assignment),
        comparison.getOperator(),
        getPartialAssignedStringValue(comparison.getRightOperand(), job, assignment), outcome
      )
      or
      (
        not exists(getPartialAssignedStringValue(comparison.getLeftOperand(), job, assignment))
        or
        not exists(getPartialAssignedStringValue(comparison.getRightOperand(), job, assignment))
      ) and
      outcome in [false, true]
    )
  )
}

private predicate separableNodeMayEvaluateTo(
  ExpressionNode node, Job job, Event event, NeedsStatus status, string assignment,
  boolean outcome
) {
  not containsDirectlyEvaluatedNeededResult(node, job) and
  assignment = getUnknownDirectNeedsAssignment(job) and
  mayEvaluateForNeedsStatus(node, job, status, outcome)
  or
  node instanceof ExpressionRoot and
  separableNodeMayEvaluateTo(node.getChild(0), job, event, status, assignment, outcome)
  or
  node instanceof UnaryExpression and
  separableNodeMayEvaluateTo(node.(UnaryExpression).getOperand(), job, event, status, assignment,
    outcome.booleanNot())
  or
  node instanceof BinaryExpression and
  node.(BinaryExpression).getOperator() = "&&" and
  (
    outcome = false and
    separableNodeMayEvaluateTo([
        node.(BinaryExpression).getLeftOperand(), node.(BinaryExpression).getRightOperand()
      ], job, event, status, assignment, false)
    or
    outcome = true and
    exists(string leftAssignment, string rightAssignment |
      separableNodeMayEvaluateTo(node.(BinaryExpression).getLeftOperand(), job, event, status,
        leftAssignment, true) and
      separableNodeMayEvaluateTo(node.(BinaryExpression).getRightOperand(), job, event, status,
        rightAssignment, true) and
      assignment = mergePartialAssignments(job, leftAssignment, rightAssignment)
    )
  )
  or
  node instanceof BinaryExpression and
  node.(BinaryExpression).getOperator() = "||" and
  (
    outcome = true and
    separableNodeMayEvaluateTo([
        node.(BinaryExpression).getLeftOperand(), node.(BinaryExpression).getRightOperand()
      ], job, event, status, assignment, true)
    or
    outcome = false and
    exists(string leftAssignment, string rightAssignment |
      separableNodeMayEvaluateTo(node.(BinaryExpression).getLeftOperand(), job, event, status,
        leftAssignment, false) and
      separableNodeMayEvaluateTo(node.(BinaryExpression).getRightOperand(), job, event, status,
        rightAssignment, false) and
      assignment = mergePartialAssignments(job, leftAssignment, rightAssignment)
    )
  )
  or
  node instanceof BinaryExpression and
  containsDirectlyEvaluatedNeededResult(node, job) and
  separableComparisonMayEvaluateTo(node.(BinaryExpression), job, event, assignment, outcome)
}

bindingset[job, assignment]
pragma[inline_late]
private int getAFixedPartialNonSuccessKind(Job job, string assignment) {
  assignment.length() = count(job.getANeededJob()) and
  exists(int index, string code |
    index in [0 .. assignment.length() - 1] and
    code = assignment.charAt(index) and
    (
      code = "f" and result = 0
      or
      code = "c" and result = 1
      or
      code = "k" and result = 2
    )
  )
}

bindingset[job, assignment]
pragma[inline_late]
private Job getAnUnknownPartialNeededJob(Job job, string assignment) {
  assignment.length() = count(job.getANeededJob()) and
  exists(int index |
    result = getNeededJobAt(job, index) and assignment.charAt(index) = "?"
  )
}

bindingset[job, assignment, needed]
pragma[inline_late]
private predicate partialAssignmentRequiresSuccess(
  Job job, string assignment, Job needed
) {
  getPartialAssignedStatus(job, assignment, needed) instanceof SuccessStatus
  or
  exists(Job dependent, JobStatus dependentStatus |
    dependent = job.getANeededJob() and
    dependentStatus = getPartialAssignedStatus(job, assignment, dependent) and
    not dependentStatus instanceof SkippedStatus and
    structurallyRequiresSuccessfulCompletionOf(dependent, needed)
  )
}

bindingset[job, assignment]
pragma[inline_late]
private predicate partialAssignmentIsConsistent(Job job, string assignment) {
  forall(Job needed |
    needed = job.getANeededJob() and partialAssignmentRequiresSuccess(job, assignment, needed)
  |
    not exists(getPartialAssignedStatus(job, assignment, needed))
    or
    getPartialAssignedStatus(job, assignment, needed) instanceof SuccessStatus
  )
}

bindingset[job, assignment]
pragma[inline_late]
private Job getAnUnconstrainedUnknownPartialNeededJob(Job job, string assignment) {
  result = getAnUnknownPartialNeededJob(job, assignment) and
  not partialAssignmentRequiresSuccess(job, assignment, result)
}

bindingset[job, assignment, summary]
pragma[inline_late]
private predicate partialAssignmentMayHaveSummary(
  Job job, string assignment, NeedsStatus summary
) {
  assignment.length() = count(job.getANeededJob()) and
  partialAssignmentIsConsistent(job, assignment) and
  forall(int index, string code |
    index in [0 .. assignment.length() - 1] and
    code = assignment.charAt(index) and
    code != "?"
  |
    code = "s"
    or
    code = "f" and summary.hasFailure() = true
    or
    code = "c" and summary.hasCancellation() = true
    or
    code = "k" and summary.hasSkip() = true
  ) and
  summary.getNonSuccessKindCount() <=
    count(getAFixedPartialNonSuccessKind(job, assignment)) +
      count(getAnUnconstrainedUnknownPartialNeededJob(job, assignment)) and
  (
    summary.hasSkip() = false
    or
    exists(assignment.indexOf("k"))
    or
    exists(Job needed |
      needed = getAnUnconstrainedUnknownPartialNeededJob(job, assignment) and
      jobMayBeSkipped(needed)
    )
  )
}

private predicate separableConditionMayHaveOutcome(
  Job job, Event event, NeedsStatus status, boolean outcome
) {
  exists(If condition, string assignment |
    condition = job.getIf() and
    condition.getATriggerEvent() = event and
    separableNodeMayEvaluateTo(condition.getConditionExpr().getRoot(), job, event, status,
      assignment, outcome) and
    partialAssignmentMayHaveSummary(job, assignment, status)
  )
}

private predicate separableConditionMayHaveOutcomeWithDirectStatus(
  Job job, Event event, NeedsStatus status, boolean outcome, Job needed, JobStatus neededStatus
) {
  exists(If condition, string assignment, string constrainedAssignment |
    condition = job.getIf() and
    condition.getATriggerEvent() = event and
    directNeededStatusMayOccurForEvent(needed, event, neededStatus) and
    separableNodeMayEvaluateTo(condition.getConditionExpr().getRoot(), job, event, status,
      assignment, outcome) and
    constrainedAssignment =
      mergePartialAssignments(job, assignment,
        getSingleStatusPartialAssignment(job, needed, neededStatus)) and
    partialAssignmentMayHaveSummary(job, constrainedAssignment, status)
  )
}

private predicate belongsToAssignedNeedsValueCondition(ExpressionNode node, Job job) {
  exists(If condition |
    condition = job.getIf() and
    node.getExpression() = condition.getConditionExpr()
  )
}

private predicate mayEvaluateForNeedsStatus(
  ExpressionNode node, Job job, NeedsStatus status, boolean outcome
) {
  belongsToAssignedNeedsValueCondition(node, job) and
  (
    node instanceof ExpressionRoot and
    mayEvaluateForNeedsStatus(node.getChild(0), job, status, outcome)
    or
    node instanceof LiteralExpression and
    node.getKind() = "BooleanLiteral" and
    node.(LiteralExpression).getValue().toLowerCase() = outcome.toString()
    or
    node instanceof UnaryExpression and
    node.(UnaryExpression).getOperator() = "!" and
    mayEvaluateForNeedsStatus(node.(UnaryExpression).getOperand(), job, status,
      outcome.booleanNot())
    or
    node instanceof BinaryExpression and
    node.(BinaryExpression).getOperator() = "&&" and
    (
      outcome = false and
      mayEvaluateForNeedsStatus([
          node.(BinaryExpression).getLeftOperand(), node.(BinaryExpression).getRightOperand()
        ], job, status, false)
      or
      outcome = true and
      mayEvaluateForNeedsStatus(node.(BinaryExpression).getLeftOperand(), job, status, true) and
      mayEvaluateForNeedsStatus(node.(BinaryExpression).getRightOperand(), job, status, true)
    )
    or
    node instanceof BinaryExpression and
    node.(BinaryExpression).getOperator() = "||" and
    (
      outcome = true and
      mayEvaluateForNeedsStatus([
          node.(BinaryExpression).getLeftOperand(), node.(BinaryExpression).getRightOperand()
        ], job, status, true)
      or
      outcome = false and
      mayEvaluateForNeedsStatus(node.(BinaryExpression).getLeftOperand(), job, status, false) and
      mayEvaluateForNeedsStatus(node.(BinaryExpression).getRightOperand(), job, status, false)
    )
    or
    node instanceof BinaryExpression and
    node.(BinaryExpression).getOperator() = ["==", "!="] and
    stringComparisonEvaluatesTo(getSummaryStringValue(node.(BinaryExpression).getLeftOperand(), job,
        status), node.(BinaryExpression).getOperator(),
      getSummaryStringValue(node.(BinaryExpression).getRightOperand(), job, status), outcome)
    or
    node instanceof BinaryExpression and
    node.(BinaryExpression).getOperator() = ["==", "!="] and
    (
      not exists(getSummaryStringValue(node.(BinaryExpression).getLeftOperand(), job, status))
      or
      not exists(getSummaryStringValue(node.(BinaryExpression).getRightOperand(), job, status))
    ) and
    outcome in [false, true]
    or
    node instanceof AccessExpression and
    exists(string value | value = getSummaryStringValue(node, job, status) |
      stringTruthinessEvaluatesTo(value, outcome)
    )
    or
    node instanceof AccessExpression and
    not exists(getSummaryStringValue(node, job, status)) and
    outcome in [false, true]
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
      node.(BinaryExpression).getOperator() = ["&&", "||", "==", "!="]
    ) and
    not node instanceof AccessExpression and
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

private newtype TConservativeNeededStatusAssignment =
  MkConservativeNeededStatusAssignment(Job job, string assignment) {
    assignment = getAConservativeNeededStatusAssignment(job)
  }

private class ConservativeNeededStatusAssignment extends TConservativeNeededStatusAssignment {
  Job getJob() { this = MkConservativeNeededStatusAssignment(result, _) }

  string getAssignment() { this = MkConservativeNeededStatusAssignment(_, result) }

  string toString() { result = this.getJob().getId() + ":" + this.getAssignment() }
}

private predicate mayEvaluateForAssignmentImpl(
  ExpressionNode node, ConservativeNeededStatusAssignment state, Event event, boolean outcome
) {
  exists(Job job, string assignment |
    job = state.getJob() and
    assignment = state.getAssignment() and
    exists(If condition |
      condition = job.getIf() and
      node.getExpression() = condition.getConditionExpr() and
      condition.getATriggerEvent() = event
    ) and
    (
    node instanceof ExpressionRoot and
    mayEvaluateForAssignmentImpl(node.getChild(0), state, event, outcome)
    or
    node instanceof LiteralExpression and
    node.getKind() = "BooleanLiteral" and
    node.(LiteralExpression).getValue().toLowerCase() = outcome.toString()
    or
    node instanceof UnaryExpression and
    mayEvaluateForAssignmentImpl(node.(UnaryExpression).getOperand(), state, event,
      outcome.booleanNot())
    or
    node instanceof BinaryExpression and
    node.(BinaryExpression).getOperator() = "&&" and
    (
      outcome = false and
      mayEvaluateForAssignmentImpl([
          node.(BinaryExpression).getLeftOperand(), node.(BinaryExpression).getRightOperand()
        ], state, event, false)
      or
      outcome = true and
      mayEvaluateForAssignmentImpl(node.(BinaryExpression).getLeftOperand(), state, event,
        true) and
      mayEvaluateForAssignmentImpl(node.(BinaryExpression).getRightOperand(), state, event,
        true)
    )
    or
    node instanceof BinaryExpression and
    node.(BinaryExpression).getOperator() = "||" and
    (
      outcome = true and
      mayEvaluateForAssignmentImpl([
          node.(BinaryExpression).getLeftOperand(), node.(BinaryExpression).getRightOperand()
        ], state, event, true)
      or
      outcome = false and
      mayEvaluateForAssignmentImpl(node.(BinaryExpression).getLeftOperand(), state, event,
        false) and
      mayEvaluateForAssignmentImpl(node.(BinaryExpression).getRightOperand(), state, event,
        false)
    )
    or
    node instanceof BinaryExpression and
    node.(BinaryExpression).getOperator() = ["==", "!="] and
    stringComparisonEvaluatesTo(getAssignedStringValue(node.(BinaryExpression).getLeftOperand(), job,
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
      stringTruthinessEvaluatesTo(value, outcome)
    )
    or
    node instanceof AccessExpression and
    not exists(getAssignedStringValue(node, job, assignment)) and
    outcome in [false, true]
    or
    node instanceof FunctionCallExpression and
    not exists(node.(FunctionCallExpression).getArgument(_)) and
    (
      node.(FunctionCallExpression).getCallee().getName().toLowerCase() = "always" and
      outcome = true
      or
      node.(FunctionCallExpression).getCallee().getName().toLowerCase() = "success" and
      (
        getAssignmentSummary(assignment).isSuccess() and outcome = true
        or
        not getAssignmentSummary(assignment).isSuccess() and outcome = false
      )
      or
      node.(FunctionCallExpression).getCallee().getName().toLowerCase() = "failure" and
      outcome = getAssignmentSummary(assignment).hasFailure()
      or
      node.(FunctionCallExpression).getCallee().getName().toLowerCase() = "cancelled" and
      outcome = getAssignmentSummary(assignment).hasCancellation()
    )
    or
    not node instanceof ExpressionRoot and
    not node instanceof UnaryExpression and
    not (
      node instanceof BinaryExpression and
      node.(BinaryExpression).getOperator() = ["&&", "||", "==", "!="]
    ) and
    not node instanceof AccessExpression and
    not (node instanceof LiteralExpression and node.getKind() = "BooleanLiteral") and
    not (
      node instanceof FunctionCallExpression and
      not exists(node.(FunctionCallExpression).getArgument(_)) and
      node.(FunctionCallExpression).getCallee().getName().toLowerCase() =
        ["always", "success", "failure", "cancelled"]
    ) and
    outcome in [false, true]
    )
  )
}

bindingset[node, job, event]
pragma[inline_late]
private predicate mayEvaluateForAssignment(
  ExpressionNode node, Job job, Event event, string assignment, boolean outcome
) {
  exists(ConservativeNeededStatusAssignment state |
    state.getJob() = job and
    state.getAssignment() = assignment and
    mayEvaluateForAssignmentImpl(node, state, event, outcome)
  )
}

private string getAConservativeNeededStatusAssignmentPrefix(Job job, int length) {
  jobConditionUsesExactNeedsAssignment(job) and
  (
    length = 0 and result = ""
    or
    exists(string prefix, Job needed, JobStatus status |
      length > 0 and
      needed = getDemandedNeededJobAt(job, length - 1) and
      (not status instanceof SkippedStatus or jobMayBeSkipped(needed)) and
      prefix = getAConservativeNeededStatusAssignmentPrefix(job, length - 1) and
      result = prefix + getStatusCode(status)
    )
  )
}

bindingset[job, assignment]
pragma[inline_late]
private boolean demandedAssignmentHasFailure(Job job, string assignment) {
  exists(Job needed |
    needed = getAConditionDemandedNeededJob(job) and
    getAssignedStatus(job, assignment, needed) instanceof FailureStatus
  ) and
  result = true
  or
  not exists(Job needed |
    needed = getAConditionDemandedNeededJob(job) and
    getAssignedStatus(job, assignment, needed) instanceof FailureStatus
  ) and
  result = false
}

bindingset[job, assignment]
pragma[inline_late]
private boolean demandedAssignmentHasCancellation(Job job, string assignment) {
  exists(Job needed |
    needed = getAConditionDemandedNeededJob(job) and
    getAssignedStatus(job, assignment, needed) instanceof CancelledStatus
  ) and
  result = true
  or
  not exists(Job needed |
    needed = getAConditionDemandedNeededJob(job) and
    getAssignedStatus(job, assignment, needed) instanceof CancelledStatus
  ) and
  result = false
}

bindingset[job, assignment]
pragma[inline_late]
private boolean demandedAssignmentHasSkip(Job job, string assignment) {
  exists(Job needed |
    needed = getAConditionDemandedNeededJob(job) and
    getAssignedStatus(job, assignment, needed) instanceof SkippedStatus
  ) and
  result = true
  or
  not exists(Job needed |
    needed = getAConditionDemandedNeededJob(job) and
    getAssignedStatus(job, assignment, needed) instanceof SkippedStatus
  ) and
  result = false
}

bindingset[job, assignment]
pragma[inline_late]
private NeedsStatus getDemandedAssignmentSummary(Job job, string assignment) {
  result =
    TNeedsStatusSummary(demandedAssignmentHasFailure(job, assignment),
      demandedAssignmentHasCancellation(job, assignment),
      demandedAssignmentHasSkip(job, assignment))
}

bindingset[job]
pragma[inline_late]
private predicate allDirectNeedsAreDemanded(Job job) {
  forall(Job needed | needed = job.getANeededJob() |
    needed = getAConditionDemandedNeededJob(job)
  )
}

bindingset[job, assignment, summary]
pragma[inline_late]
private predicate assignmentSummaryIncludesDemandedStatuses(
  Job job, string assignment, NeedsStatus summary
) {
  allDirectNeedsAreDemanded(job) and
  summary = getDemandedAssignmentSummary(job, assignment)
  or
  not allDirectNeedsAreDemanded(job) and
  forall(Job needed | needed = getAConditionDemandedNeededJob(job) |
    exists(JobStatus status |
      status = getAssignedStatus(job, assignment, needed) and
      (
        status instanceof SuccessStatus
        or
        status instanceof FailureStatus and summary.hasFailure() = true
        or
        status instanceof CancelledStatus and summary.hasCancellation() = true
        or
        status instanceof SkippedStatus and summary.hasSkip() = true
      )
    )
  )
}

private string getAConservativeNeededStatusAssignment(Job job) {
  exists(string assignment, NeedsStatus status |
    assignment =
      getAConservativeNeededStatusAssignmentPrefix(job,
        count(getAConditionDemandedNeededJob(job))) and
    demandedNeedsAssignmentIsConsistent(job, assignment) and
    assignmentSummaryIncludesDemandedStatuses(job, assignment, status) and
    result = assignment + ":" + status.getName()
  )
}

bindingset[job, event, assignment]
private predicate decisionMayHaveOutcomeForExactAssignment(
  Job job, Event event, string assignment, boolean outcome
) {
  jobConditionUsesExactNeedsAssignment(job) and
  decisionMayHaveOutcomeForAssignment(job, event, assignment, outcome)
  or
  not jobConditionUsesExactNeedsAssignment(job) and
  decisionMayHaveOutcome(job, event, getAssignmentSummary(assignment), outcome)
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

private predicate jobConditionDependsOnNeedsState(Job job) {
  jobConditionContainsAssignedNeedsValue(job)
  or
  jobConditionHasStatusCheckFunction(job)
}

private predicate jobConditionHasStatusCheckFunction(Job job) {
  exists(If condition | condition = job.getIf() | hasStatusCheckFunction(condition))
}

private predicate prerequisiteHasParsedCondition(Job job) {
  exists(Job prerequisite, If condition |
    prerequisite = getANeededAncestor(job) and
    condition = prerequisite.getIf() and
    exists(condition.getConditionExpr().getRoot())
  )
}

private predicate prerequisiteClosureContainsReusableCall(Job job) {
  exists(Job prerequisite |
    prerequisite = job or prerequisite = getANeededAncestor(job)
  |
    exists(getCalledReusableWorkflow(prerequisite))
  )
}

private predicate canUseOwnConditionExecutionFastPath(Job job) {
  not jobConditionDependsOnNeedsState(job) and
  not prerequisiteHasParsedCondition(job) and
  not prerequisiteClosureContainsReusableCall(job)
}

/** Holds if `job` may execute for `event`, accounting for all transitive prerequisites. */
bindingset[job, event]
predicate jobMayExecuteForEvent(Job job, Event event) {
  job.getATriggerEvent() = event and
  (
    canUseOwnConditionExecutionFastPath(job) and ownConditionMayHaveOutcome(job, event, true)
    or
    not canUseOwnConditionExecutionFastPath(job) and
    not jobConditionUsesExactNeedsAssignment(job) and
    exists(NeedsStatus needsStatus |
      needsStatusMayOccurForEvent(job, event, needsStatus) and
      decisionMayHaveOutcome(job, event, needsStatus, true)
    )
    or
    not canUseOwnConditionExecutionFastPath(job) and
    jobConditionUsesExactNeedsAssignment(job) and
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
    status = getAPossibleExecutedJobConclusionForEvent(job, event)
    or
    status instanceof SkippedStatus and
    (
      not jobConditionUsesExactNeedsAssignment(job) and
      exists(NeedsStatus needsStatus |
        needsStatusMayOccurForEvent(job, event, needsStatus) and
        decisionMayHaveOutcome(job, event, needsStatus, false)
      )
      or
      jobConditionUsesExactNeedsAssignment(job) and
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
  jobConditionHasStatusCheckFunction(job) and
  neededJob = job.getANeededJob() and
  job.getATriggerEvent() = event and
  (
    jobConditionUsesSeparableNeedsAssignment(job) and
    exists(NeedsStatus status |
      separableConditionMayHaveOutcomeWithDirectStatus(job, event, status, true, neededJob,
        neededStatus)
    )
    or
    jobConditionUsesExactNeedsAssignment(job) and
    exists(string assignment |
      assignment = getANeededStatusAssignment(job, event) and
      getAssignedStatus(job, assignment, neededJob) = neededStatus and
      decisionMayHaveOutcomeForExactAssignment(job, event, assignment, true)
    )
    or
    not jobConditionUsesExactNeedsAssignment(job) and
    not jobConditionUsesSeparableNeedsAssignment(job) and
    exists(NeedsStatus status |
      status = getAConservativeNeedsStatusForDirectStatus(job, neededJob, neededStatus) and
      decisionMayHaveOutcome(job, event, status, true)
    )
  )
}

private predicate jobExecutionDirectlyRequiresSuccessfulCompletionOf(
  Job job, Job neededJob, Event event
) {
  not jobConditionHasStatusCheckFunction(job) and
  neededJob = job.getANeededJob() and
  job.getATriggerEvent() = event and
  jobMayExecuteForEvent(job, event)
  or
  jobConditionHasStatusCheckFunction(job) and
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
  or
  exists(Job demandedNeeded, SkippedStatus skipped |
    demandedNeeded = getAConditionDemandedNeededJob(job) and
    jobMayExecuteForEvent(job, event) and
    not jobMayExecuteWithDirectNeededStatus(job, event, demandedNeeded, skipped) and
    jobExecutionRequiresSuccessfulCompletionOf(demandedNeeded, neededJob, event)
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
    not decision.getJob().getStrategy().hasMatrix() and
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
    not exists(getCalledReusableWorkflow(execution.getJob())) and
    completion.getInstance() = execution.getInstance() and
    successor = completion
  )
  or
  exists(MatrixJobExecutionNode execution, WorkflowEntryNode entry |
    predecessor = execution and
    entry.getWorkflow() = getCalledReusableWorkflow(execution.getJob()) and
    successor = entry
  )
  or
  exists(MatrixJobCompletionNode completion, MatrixJobFanInNode fanIn |
    predecessor = completion and
    completion.getJob() = fanIn.getJob() and
    (
      not exists(getCalledReusableWorkflow(completion.getJob()))
      or
      exists(Event event |
        reusableMatrixInstanceMayCompleteForEvent(completion.getInstance(), event,
          completion.getStatus())
      )
    ) and
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
    exists(Event event |
      completion.getJob().getATriggerEvent() = event and
      reusableWorkflowMayCompleteForEvent(exit.getWorkflow(), event, completion.getStatus())
    ) and
    successor = completion
  )
  or
  exists(WorkflowExitNode exit, MatrixJobCompletionNode completion, Event event |
    predecessor = exit and
    exit.getWorkflow() = getCalledReusableWorkflow(completion.getJob()) and
    reusableMatrixInstanceMayCompleteForEvent(completion.getInstance(), event,
      completion.getStatus()) and
    successor = completion
  )
}

private predicate synchronizationSuccessorForEvent(Node predecessor, Node successor, Event event) {
  synchronizationSuccessor(predecessor, successor) and
  not predecessor instanceof JobDecisionNode and
  not predecessor instanceof NeedsJoinNode and
  not predecessor instanceof MatrixJobCompletionNode and
  not predecessor instanceof WorkflowExitNode
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
  exists(JobDecisionNode decision, MatrixJobExecutionNode execution |
    predecessor = decision and
    execution.getJob() = decision.getJob() and
    needsStatusMayOccurForEvent(decision.getJob(), event, decision.getNeedsStatus()) and
    decisionMayHaveOutcome(decision.getJob(), event, decision.getNeedsStatus(), true) and
    successor = execution
  )
  or
  exists(JobDecisionNode decision, WorkflowEntryNode entry |
    predecessor = decision and
    not decision.getJob().getStrategy().hasMatrix() and
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
  or
  exists(WorkflowExitNode exit, JobCompletionNode completion |
    predecessor = exit and
    exit.getWorkflow() = getCalledReusableWorkflow(completion.getJob()) and
    not completion.getStatus() instanceof SkippedStatus and
    reusableWorkflowMayCompleteForEvent(exit.getWorkflow(), event, completion.getStatus()) and
    successor = completion
  )
  or
  exists(WorkflowExitNode exit, MatrixJobCompletionNode completion |
    predecessor = exit and
    exit.getWorkflow() = getCalledReusableWorkflow(completion.getJob()) and
    reusableMatrixInstanceMayCompleteForEvent(completion.getInstance(), event,
      completion.getStatus()) and
    successor = completion
  )
  or
  exists(MatrixJobCompletionNode completion, MatrixJobFanInNode fanIn |
    predecessor = completion and
    synchronizationSuccessor(completion, fanIn) and
    jobMayCompleteForEvent(fanIn.getJob(), event, fanIn.getStatus()) and
    successor = fanIn
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
