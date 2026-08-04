import actions
import codeql.actions.ExpressionEvaluation as Evaluation

query predicate localSources(string workflow, string sourceWorkflow, string sourceEvent) {
  exists(Event event, Workflow source |
    event.getName() = "workflow_run" and
    workflow = event.getEnclosingWorkflow().getName() and
    source = event.getALocalWorkflowRunSource() and
    sourceWorkflow = source.getName() and
    sourceEvent = event.getALocalWorkflowRunSourceEvent().getName()
  )
}

query predicate externallyTriggerable(string workflow) {
  exists(Event event |
    event.getName() = "workflow_run" and
    workflow = event.getEnclosingWorkflow().getName() and
    event.isExternallyTriggerable()
  )
}

query predicate sourceConditionFeasible(string workflow, string job, string sourceEvent) {
  exists(LocalJob localJob, Event event, Event source |
    workflow = localJob.getEnclosingWorkflow().getName() and
    job = localJob.getId() and
    event = localJob.getATriggerEvent() and
    event.getName() = "workflow_run" and
    source = event.getALocalWorkflowRunSourceEvent() and
    sourceEvent = source.getName() and
    Evaluation::isConditionFeasible(localJob.getIf(), event, source)
  )
}

query predicate externalSourceExecution(string workflow, string job) {
  exists(LocalJob localJob, Event event |
    workflow = localJob.getEnclosingWorkflow().getName() and
    job = localJob.getId() and
    event = localJob.getATriggerEvent() and
    event.getName() = "workflow_run" and
    workflowRunAwarePrivilegedContext(localJob, event)
  )
}
