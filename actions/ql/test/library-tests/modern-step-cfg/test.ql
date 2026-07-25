import codeql.actions.Ast
import codeql.actions.Cfg as Cfg

private predicate cfgMayReach(AstNode source, AstNode target) {
  exists(Cfg::Node sourceNode, Cfg::Node targetNode |
    sourceNode.getAstNode() = source and
    targetNode.getAstNode() = target and
    targetNode = sourceNode.getASuccessor*()
  )
}

private string stepName(Step step) {
  result = step.getId()
  or
  not exists(step.getId()) and result = step.toString()
}

query predicate typedSteps(string job, string kind, string step) {
  exists(LocalJob local, Step child |
    job = local.getId() and
    local.getAStep() = child and
    step = stepName(child) and
    (
      child instanceof Run and kind = "run"
      or
      child instanceof UsesStep and kind = "uses"
      or
      child instanceof WaitStep and kind = "wait"
      or
      child instanceof WaitAllStep and kind = "wait-all"
      or
      child instanceof CancelStep and kind = "cancel"
      or
      child instanceof ParallelStep and kind = "parallel"
    )
  )
}

query predicate backgroundSteps(string job, string step) {
  exists(LocalJob local, BackgroundStep background |
    job = local.getId() and local.getAStep() = background and step = background.getId()
  )
}

query predicate backgroundBodies(string job, string step, string kind, string body) {
  exists(LocalJob local, BackgroundStep background |
    job = local.getId() and
    local.getAStep() = background and
    step = background.getId() and
    (
      background instanceof Run and
      kind = "run" and
      body = background.(Run).getScript().toString()
      or
      background instanceof UsesStep and
      kind = "uses" and
      body = background.(UsesStep).getCallee()
    )
  )
}

query predicate unjoinedBackgroundSteps(string job, string step) {
  exists(LocalJob local, BackgroundStep background |
    job = local.getId() and
    local.getAStep() = background and
    not exists(background.getBarrier()) and
    step = background.getId()
  )
}

query predicate waitTargets(string job, string waitStep, string target) {
  exists(LocalJob local, WaitStep wait |
    job = local.getId() and
    local.getAStep() = wait and
    waitStep = wait.getId() and
    target = wait.getATargetId()
  )
}

query predicate cancelTargets(string job, string cancelStep, string target) {
  exists(LocalJob local, CancelStep cancel |
    job = local.getId() and
    local.getAStep() = cancel and
    cancelStep = cancel.getId() and
    target = cancel.getTargetId()
  )
}

query predicate parallelChildren(string job, string kind, string childId) {
  exists(LocalJob local, ParallelStep parallel, Step child |
    job = local.getId() and
    local.getAStep() = parallel and
    parallel.getAStep() = child and
    childId = child.getId() and
    (
      child instanceof Run and kind = "run"
      or
      child instanceof UsesStep and kind = "uses"
    )
  )
}

query predicate containedSteps(string job, string step) {
  exists(LocalJob local, Step child |
    job = local.getId() and
    local.getAContainedStep() = child and
    step = stepName(child)
  )
}

query predicate stepReachability(string job, string source, string target) {
  exists(LocalJob local, Step sourceStep, Step targetStep |
    job = local.getId() and
    sourceStep.getEnclosingJob() = local and
    targetStep.getEnclosingJob() = local and
    source = stepName(sourceStep) and
    target = stepName(targetStep) and
    cfgMayReach(sourceStep, targetStep)
  )
}

query predicate backgroundBodyReachability(string job, string source, string target) {
  exists(LocalJob local, Run background, Step targetStep |
    job = local.getId() and
    background.getEnclosingJob() = local and
    background instanceof BackgroundStep and
    targetStep.getEnclosingJob() = local and
    source = background.getId() + " body" and
    target = stepName(targetStep) and
    cfgMayReach(background.getScript(), targetStep)
  )
}

query predicate backgroundArgumentReachability(string job, string source, string target) {
  exists(LocalJob local, UsesStep background, WaitStep wait |
    job = local.getId() and
    background.getEnclosingJob() = local and
    background instanceof BackgroundStep and
    wait.getEnclosingJob() = local and
    source = background.getId() + " argument" and
    target = wait.getId() and
    cfgMayReach(background.getArgumentExpr("script"), wait)
  )
}

query predicate barrierCompletionEdges(string job, string background, string barrier) {
  exists(
    BackgroundStep backgroundStep, Step barrierStep, Cfg::Node completionNode,
    Cfg::Node barrierNode
  |
    job = backgroundStep.getEnclosingJob().getId() and
    background = backgroundStep.getId() and
    backgroundStep.getBarrier() = barrierStep and
    not barrierStep instanceof CancelStep and
    barrier = barrierStep.getId() and
    completionNode.getAstNode() = backgroundStep.getCompletion() and
    barrierNode.getAstNode() = barrierStep and
    barrierNode = completionNode.getASuccessor()
  )
}

query predicate implicitExitReachability(string job, string background) {
  exists(
    LocalJob local, BackgroundStep backgroundStep, Cfg::Node completionNode, Cfg::ExitNode exit
  |
    job = local.getId() and
    local.getAStep() = backgroundStep and
    not exists(backgroundStep.getBarrier()) and
    background = backgroundStep.getId() and
    completionNode.getAstNode() = backgroundStep.getCompletion() and
    exit.getScope() = local.getWorkflow() and
    exit = completionNode.getASuccessor+()
  )
}

query predicate forbiddenReachability(string description) {
  exists(LocalJob local, Run background, Step foreground |
    local.getId() = "explicit-wait" and
    local.getAStep() = background and
    background.getId() = "background-run" and
    local.getAStep() = foreground and
    foreground.getId() = "foreground" and
    cfgMayReach(background.getScript(), foreground) and
    description = "background body reaches intervening foreground step"
  )
  or
  exists(LocalJob local, BackgroundStep background, Step foreground |
    local.getId() = "explicit-wait" and
    local.getAStep() = background and
    background.getId() = "background-run" and
    local.getAStep() = foreground and
    foreground.getId() = "foreground" and
    background.getAFollowingStep() = foreground and
    description = "background syntactically precedes intervening foreground step"
  )
  or
  exists(CancelStep cancel, BackgroundStep background |
    cancel.getTargetStep() = background and
    cfgMayReach(background.getCompletion(), cancel) and
    description = "cancel waits for natural background completion"
  )
  or
  exists(ParallelStep parallel, Step left, Step right |
    parallel.getAStep() = left and
    left.getId() = "parallel-run" and
    parallel.getAStep() = right and
    right.getId() = "parallel-use" and
    (
      cfgMayReach(left, right) or cfgMayReach(right, left)
    ) and
    description = "parallel siblings are ordered"
  )
}

query predicate backgroundFollowingSteps(string job, string background, string following) {
  exists(LocalJob local, BackgroundStep source, Step target |
    job = local.getId() and
    local.getAStep() = source and
    background = source.getId() and
    source.getAFollowingStep() = target and
    following = stepName(target)
  )
}

query predicate cancelContinuation(string job, string cancelStep, string successor) {
  exists(LocalJob local, CancelStep cancel, Step next |
    job = local.getId() and
    local.getAStep() = cancel and
    cancelStep = cancel.getId() and
    next.getEnclosingJob() = local and
    next.getId() = "after-cancel" and
    successor = next.getId() and
    cfgMayReach(cancel, next)
  )
}

query predicate skippedBackgroundContinuation(string job, string waitStep, string successor) {
  exists(LocalJob local, BackgroundStep background, WaitStep wait, Step next |
    local.getId() = "skipped-background" and
    job = local.getId() and
    local.getAStep() = background and
    background.getId() = "maybe-background" and
    local.getAStep() = wait and
    wait.getId() = "wait-skipped" and
    local.getAStep() = next and
    next.getId() = "after-skipped" and
    waitStep = wait.getId() and
    successor = next.getId() and
    cfgMayReach(background.getIf(), wait) and
    cfgMayReach(wait, next)
  )
}

query predicate nestedBackgroundExit(string job, string background) {
  exists(
    LocalJob local, BackgroundStep source, Cfg::Node completionNode, Cfg::ExitNode exit
  |
    local.getId() = "nested-background" and
    job = local.getId() and
    local.getAContainedStep() = source and
    source.getId() = "nested-background-run" and
    background = source.getId() and
    not exists(source.getBarrier()) and
    completionNode.getAstNode() = source.getCompletion() and
    exit.getScope() = local.getWorkflow() and
    exit = completionNode.getASuccessor+()
  )
}

query predicate disabledWaitAll(string job, string step, string classification) {
  exists(LocalJob local, Step wait |
    local.getId() = "disabled-wait-all" and
    job = local.getId() and
    local.getAStep() = wait and
    wait.getId() = "disabled-wait" and
    step = wait.getId() and
    if wait instanceof WaitAllStep
    then classification = "barrier"
    else classification = "no-op"
  )
}
