import codeql.actions.PullRequestAutomation
import codeql.actions.security.PoisonableSteps
import codeql.actions.security.UntrustedCheckoutQuery

query predicate remoteSubmoduleUpdates(string step) {
  step = any(RemoteSubmoduleUpdateStep update).getId()
}

query predicate localPullRequestCreators(string step) {
  step = any(ExternallyInfluencedLocalPullRequestStep creator).getId()
}

query predicate workflowTriggeringLabels(string step, string label) {
  exists(WorkflowTriggeringPullRequestLabelStep labeler |
    step = labeler.getId() and label = labeler.getAddedLabel()
  )
}

query predicate requiredLabels(string job, string label) {
  exists(LocalJob target |
    target.getEnclosingWorkflow().getName() = "Privileged agent" and
    job = target.getId() and
    conditionRequiresPullRequestLabel(target.getIf(), label)
  )
}

query predicate requiredAutomationControls(string job, string kind, string value) {
  exists(LocalJob target |
    target.getEnclosingWorkflow().getName() = "Privileged agent" and
    job = target.getId() and
    conditionRequiresPullRequestAutomationControl(target.getIf(), kind, value)
  )
}

query predicate sameRepositoryGuards(string job) {
  exists(LocalJob target |
    target.getEnclosingWorkflow().getName() = "Privileged agent" and
    job = target.getId() and
    conditionRequiresSameRepositoryPullRequestHead(target.getIf())
  )
}

query predicate automatedLabelTransitions(string targetWorkflow, string label, string sourceWorkflow) {
  exists(Event target, Event source |
    target.getEnclosingWorkflow().getName() = "Privileged agent" and
    target.getName() = "pull_request" and
    source = getAnAutomatedLocalPullRequestLabelSource(target, label) and
    targetWorkflow = target.getEnclosingWorkflow().getName() and
    sourceWorkflow = source.getEnclosingWorkflow().getName()
  )
}

query predicate automatedControlTransitions(
  string targetWorkflow, string kind, string value, string sourceWorkflow
) {
  exists(Event target, Event source |
    target.getEnclosingWorkflow().getName() = "Privileged agent" and
    target.getName() = "pull_request" and
    source = getAnAutomatedLocalPullRequestControlSource(target, kind, value) and
    targetWorkflow = target.getEnclosingWorkflow().getName() and
    sourceWorkflow = source.getEnclosingWorkflow().getName()
  )
}

query predicate automatedLocalPullRequestCriticalCheckout(
  string workflow, string checkout, string execution
) {
  exists(PRHeadCheckoutStep checkoutStep, PoisonableStep poisonable, Event event |
    criticalSeverityAutomatedLocalPullRequestCheckout(checkoutStep, poisonable, event) and
    workflow = checkoutStep.getEnclosingWorkflow().getName() and
    checkout = checkoutStep.getId() and
    execution = poisonable.getId()
  )
}
