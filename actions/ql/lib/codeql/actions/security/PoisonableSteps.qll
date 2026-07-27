import actions
private import codeql.util.FilePath

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

bindingset[run]
private string getACommandText(Run run) {
  result = run.getScript().getACommand()
  or
  run.getShell().matches(["sh%", "zsh%", "fish%", "pwsh%"]) and
  result = run.getScript().getRawScript().splitAt("\n").splitAt(";").trim() and
  result != "" and
  not result.matches("#%")
}

class LocalScriptExecutionRunStep extends PoisonableStep, Run {
  string path;

  LocalScriptExecutionRunStep() {
    exists(string cmd, string regexp, int path_group | cmd = getACommandText(this) |
      poisonableLocalScriptsDataModel(regexp, path_group) and
      path = cmd.regexpCapture(regexp, path_group)
    )
    or
    // Handles scripts passed to source, sh, bash, zsh, or fish, including quoted paths,
    // mixed literal/GitHub-expression paths, and trailing arguments:
    //   source "./scripts/setup.sh"
    //   bash candidate-${{ github.run_id }}/proof.sh --verbose
    // Does not resolve shell wrappers, shell paths, or options preceding the script path:
    //   env bash ./scripts/build.sh
    //   /bin/bash ./scripts/build.sh
    //   bash -e ./scripts/build.sh
    exists(string cmd |
      cmd = getACommandText(this) and
      path =
        cmd.regexpCapture("(?i)^\\s*(source|sh|bash|zsh|fish)\\s+(\"[^\"]+\"|'[^']+'|[^\\s]+)", 2)
    )
    or
    // Handles path-only PowerShell scripts, optionally using the call or dot-source operator:
    //   .\scripts\build.ps1
    //   & ".\scripts\build.ps1"
    //   . './scripts/setup.ps1'
    // Does not handle scripts launched through pwsh/powershell or with trailing arguments:
    //   pwsh -File .\scripts\build.ps1
    //   .\scripts\build.ps1 -Configuration Release
    exists(string cmd |
      cmd = getACommandText(this) and
      path =
        cmd.regexpCapture("(?i)^\\s*(?:&\\s+|\\.\\s+)?(\"[^\"]+\\.ps1\"|'[^']+\\.ps1'|(?:\\.\\\\|\\./)[^\\s]+\\.ps1)\\s*$",
          1)
    )
  }

  string getRawPath() { result = trimQuotes(path) }

  string getPath() { result = getNormalizedPoisonablePath(this.getRawPath()) }
}

class LocalActionUsesStep extends PoisonableStep, UsesStep {
  LocalActionUsesStep() { this.getCallee().matches("./%") }

  string getPath() { result = getNormalizedPoisonablePath(this.getCallee()) }
}

private class PoisonablePathInput extends NormalizableFilepath {
  PoisonablePathInput() {
    exists(LocalScriptExecutionRunStep step |
      not hasUnresolvedActionsPathSyntax(step.getRawPath()) and
      this = canonicalizeActionsPathSyntax(step.getRawPath())
    )
    or
    exists(LocalActionUsesStep step |
      not hasUnresolvedActionsPathSyntax(step.getCallee()) and
      this = canonicalizeActionsPathSyntax(step.getCallee())
    )
  }
}

bindingset[rawPath]
private string getNormalizedPoisonablePath(string rawPath) {
  hasUnresolvedActionsPathSyntax(rawPath) and result = "?"
  or
  exists(PoisonablePathInput path, string normalized |
    path = canonicalizeActionsPathSyntax(rawPath) and
    normalized = path.getNormalizedPath() and
    if normalized = [".", "GITHUB_WORKSPACE"]
    then result = "GITHUB_WORKSPACE/"
    else
      if
        normalized.matches("GITHUB_WORKSPACE/%") or
        normalized.matches("/%") or
        normalized.regexpMatch("^[A-Za-z]:/.*") or
        normalized = ".." or
        normalized.matches("../%")
      then result = normalized
      else result = "GITHUB_WORKSPACE/" + normalized
  )
}
