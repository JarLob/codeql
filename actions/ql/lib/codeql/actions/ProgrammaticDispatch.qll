import codeql.actions.Ast

bindingset[dispatch, argumentName, propertyName]
pragma[inline_late]
private Expression getJsonObjectPropertyExpr(
  UsesStep dispatch, string argumentName, string propertyName
) {
  exists(string payload, string key, int keyOffset, int expressionOffset, string between |
    result = dispatch.getArgumentExpr(argumentName) and
    payload = dispatch.getArgument(argumentName) and
    key = "\"" + propertyName + "\"" and
    keyOffset = payload.indexOf(key) and
    expressionOffset = payload.indexOf(result.getRawExpression()) and
    keyOffset >= 0 and
    expressionOffset > keyOffset + key.length() and
    between = payload.substring(keyOffset + key.length(), expressionOffset) and
    between.trim() = [":", ":\""]
  )
}

/** A call to `benc-uk/workflow-dispatch` with a statically resolved local target. */
class WorkflowDispatchStep extends UsesStep {
  WorkflowDispatchStep() { this.getCallee().toLowerCase() = "benc-uk/workflow-dispatch" }

  private string getTargetReference() {
    result = this.getArgument("workflow").trim() and
    not exists(this.getArgumentExpr("workflow"))
  }

  private predicate targetsWorkflow(Workflow workflow) {
    exists(string target |
      target = this.getTargetReference() and
      (
        workflow.getName() = target
        or
        workflow.getLocation().getFile().getBaseName() = target
        or
        workflow.getLocation().getFile().getRelativePath() = target
        or
        workflow.getLocation().getFile().getRelativePath().matches("%/" + target)
      )
    )
  }

  Workflow getTargetWorkflow() {
    not exists(this.getArgument("repo")) and
    result.isInSameRepositoryAs(this.getEnclosingWorkflow()) and
    this.targetsWorkflow(result) and
    exists(result.getOn().getAnEvent().getInput(_))
  }

  Event getTargetEvent() {
    this.getTargetWorkflow().getOn().getAnEvent() = result and
    result.getName() = "workflow_dispatch"
  }

  /** Gets an expression passed to the target input named `name`. */
  bindingset[this, name]
  pragma[inline_late]
  Expression getInputExpr(string name) { result = getJsonObjectPropertyExpr(this, "inputs", name) }
}

/** A call to `peter-evans/repository-dispatch` with statically resolved local targets. */
class RepositoryDispatchStep extends UsesStep {
  RepositoryDispatchStep() { this.getCallee().toLowerCase() = "peter-evans/repository-dispatch" }

  private string getEventType() {
    result = this.getArgument("event-type").trim() and
    not exists(this.getArgumentExpr("event-type"))
  }

  Event getTargetEvent() {
    not exists(this.getArgument("repository")) and
    result.getName() = "repository_dispatch" and
    result.getEnclosingWorkflow().isInSameRepositoryAs(this.getEnclosingWorkflow()) and
    result.acceptsActivityType(this.getEventType())
  }
}

/** The `client-payload` expression of a `peter-evans/repository-dispatch` step. */
class RepositoryDispatchPayloadExpression extends Expression {
  RepositoryDispatchStep dispatch;

  RepositoryDispatchPayloadExpression() { dispatch.getArgumentExpr("client-payload") = this }

  RepositoryDispatchStep getDispatch() { result = dispatch }
}

/** An access to a top-level `workflow_dispatch` event input. */
class WorkflowDispatchInputAccessExpression extends Expression {
  Event event;
  string inputName;

  WorkflowDispatchInputAccessExpression() {
    event = this.getATriggerEvent() and
    event.getName() = "workflow_dispatch" and
    this.getNormalizedExpression().toLowerCase() = "github.event.inputs." + inputName and
    inputName != ""
  }

  Event getEvent() { result = event }

  string getInputName() { result = inputName }
}

/** An access to a top-level `repository_dispatch` client-payload property. */
class RepositoryDispatchPayloadAccessExpression extends Expression {
  Event event;
  string payloadName;

  RepositoryDispatchPayloadAccessExpression() {
    event = this.getATriggerEvent() and
    event.getName() = "repository_dispatch" and
    this.getNormalizedExpression().toLowerCase() = "github.event.client_payload." + payloadName and
    payloadName != ""
  }

  Event getEvent() { result = event }

  string getPayloadName() { result = payloadName }
}

/** Gets an event whose workflow programmatically dispatches `target`. */
Event getADispatchCallerEvent(Event target) {
  exists(WorkflowDispatchStep dispatch |
    dispatch.getTargetEvent() = target and result = dispatch.getATriggerEvent()
  )
  or
  exists(RepositoryDispatchStep dispatch |
    dispatch.getTargetEvent() = target and result = dispatch.getATriggerEvent()
  )
}
