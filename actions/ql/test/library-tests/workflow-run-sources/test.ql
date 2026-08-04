import actions
import codeql.actions.ExpressionEvaluation as Evaluation
import codeql.actions.ast.internal.WorkflowTriggerGlob as WorkflowTriggerGlob

query predicate globMatches(string pattern, string input) {
  (
    pattern = "za?" and input = ["z", "za"]
    or
    pattern = "z+" and input = ["z", "zz"]
    or
    pattern = "foo/*" and input = "foo/bar"
    or
    pattern = "foo/**" and input = "foo/bar/baz"
    or
    pattern = "**/release" and input = ["newrelease", "path/release"]
    or
    pattern = "z\\*" and input = "z*"
    or
    pattern = "[a-c]z[B-U]" and input = "bzM"
    or
    pattern = "v[0-9]+.[0-9]+.[0-9]+-*" and input = "v1.2.3-beta"
    or
    pattern = "releases\\/alpha" and input = "releases/alpha"
    or
    pattern = "c\\+\\+.md" and input = "c++.md"
    or
    pattern = "(?:a)" and input = "(:a)"
    or
    pattern = "[A-z]" and input = "_"
    or
    pattern = "" and input = ""
    or
    pattern = "🎬 Setup" and input = "🎬 Setup"
  ) and
  WorkflowTriggerGlob::patternMatches(pattern, input)
}

query predicate globDoesNotMatch(string pattern, string input) {
  (
    pattern = "foo/*" and input = "foo/bar/baz"
    or
    pattern = "za?" and input = "zaa"
    or
    pattern = "z\\*" and input = "zz"
    or
    pattern = "[a-c]z[B-U]" and input = "bzm"
  ) and
  not WorkflowTriggerGlob::patternMatches(pattern, input)
}

query predicate invalidGlob(string pattern) {
  pattern =
    [
      "***", "********", "foo*+", "foo++", "[9-1]", "[9-a]", "[0-9", "[-9", "a??", "\\", "??", "*?",
      "a**?", "a+?", "[^^]", "[^a^]", "a**+", "foo[-9[*", "foo[[[[[[[]0-9]", "[[:word:]]",
      "*[a-b][*", "[0-9]++"
    ] and
  not WorkflowTriggerGlob::isValid(pattern)
}

query predicate negativeGlob(string pattern, string input) {
  pattern = "!foo" and
  input = "foo" and
  WorkflowTriggerGlob::isNegative(pattern) and
  WorkflowTriggerGlob::patternMatches(pattern, input)
}

query predicate localSources(string workflow, string sourceWorkflow, string sourceEvent) {
  exists(Event event, Workflow source, Event sourceTrigger |
    event.getName() = "workflow_run" and
    workflow = event.getEnclosingWorkflow().getName() and
    source = event.getALocalWorkflowRunSource() and
    sourceWorkflow = source.getName() and
    sourceTrigger = event.getALocalWorkflowRunSourceEvent() and
    sourceTrigger.getEnclosingWorkflow() = source and
    sourceEvent = sourceTrigger.getName()
  )
}

query predicate externallyTriggerable(string workflow) {
  exists(Event event |
    event.getName() = "workflow_run" and
    workflow = event.getEnclosingWorkflow().getName() and
    event.isExternallyTriggerable()
  )
}

query predicate unresolvedSource(string workflow) {
  exists(Event event |
    event.getName() = "workflow_run" and
    workflow = event.getEnclosingWorkflow().getName() and
    event.hasUnresolvedWorkflowRunSource()
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
