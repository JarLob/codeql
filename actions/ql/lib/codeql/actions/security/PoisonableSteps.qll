import actions

abstract class PoisonableStep extends Step { }

class DangerousActionUsesStep extends PoisonableStep, UsesStep {
  DangerousActionUsesStep() { poisonableActionsDataModel(this.getCallee()) }
}

class PoisonableCommandStep extends PoisonableStep, Run {
  PoisonableCommandStep() {
    exists(string regexp |
      poisonableCommandsDataModel(regexp) and
      this.getScript().getACommand().regexpMatch(regexp)
    )
  }
}

private predicate reusableInputCommandMayInvoke(Run run, Event event) {
  exists(
    InputsExpression access, Input input, ReusableWorkflow workflow, ExternalJob caller,
    string regexp
  |
    run.getAChildNode*() = access and
    access.getTarget() = input and
    workflow = run.getEnclosingWorkflow() and
    workflow.getInput(input.getName()) = input and
    workflow.getACaller() = caller and
    caller.getATriggerEvent() = event and
    poisonableCommandsDataModel(regexp) and
    caller.getArgument(input.getName()).regexpMatch(regexp)
  )
}

/** A run step that invokes a modeled poisonable command supplied by a reusable workflow caller. */
class ReusableInputCommandStep extends PoisonableStep, Run {
  ReusableInputCommandStep() { exists(Event event | reusableInputCommandMayInvoke(this, event)) }

  predicate mayInvokePoisonableCommandForEvent(Event event) {
    reusableInputCommandMayInvoke(this, event)
  }
}

class JavascriptImportUsesStep extends PoisonableStep, UsesStep {
  JavascriptImportUsesStep() {
    exists(string script, string line |
      this.getCallee() = "actions/github-script" and
      script = this.getArgument("script") and
      line = script.splitAt("\n").trim() and
      // const { default: foo } = await import('${{ github.workspace }}/scripts/foo.mjs')
      // const script = require('${{ github.workspace }}/scripts/test.js');
      // const script = require('./scripts');
      line.regexpMatch(".*(import|require)\\(('|\")(\\./|.*github.workspace).*")
    )
  }
}

class SetupNodeUsesStep extends PoisonableStep, UsesStep {
  SetupNodeUsesStep() {
    this.getCallee() = "actions/setup-node" and
    this.getArgument("cache") = "yarn"
  }
}

class LocalScriptExecutionRunStep extends PoisonableStep, Run {
  string path;

  LocalScriptExecutionRunStep() {
    exists(string cmd, string regexp, int path_group | cmd = this.getScript().getACommand() |
      poisonableLocalScriptsDataModel(regexp, path_group) and
      path = cmd.regexpCapture(regexp, path_group)
    )
  }

  string getPath() { result = normalizePath(path.splitAt(" ")) }
}

class LocalActionUsesStep extends PoisonableStep, UsesStep {
  LocalActionUsesStep() { this.getCallee().matches("./%") }

  string getPath() { result = normalizePath(this.getCallee()) }
}
