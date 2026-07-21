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
      mayEvaluateToBoolean(condition.getConditionExpr().getRoot(), event, outcome)
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
      mayEvaluateToBooleanAfterNeedsState(condition.getConditionExpr().getRoot(), event,
        needsStatus.hasFailure(), needsStatus.hasCancellation(), needsStatus.hasSkip(), outcome)
      or
      exists(condition.getConditionExpr().getRoot()) and
      not hasStatusCheckFunction(condition) and
      (
        needsStatus.isSuccess() and
        mayEvaluateToBoolean(condition.getConditionExpr().getRoot(), event, outcome)
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
  not predecessor instanceof JobDecisionNode
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
