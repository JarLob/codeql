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
    exists(string cmd, string regexp, int path_group | cmd = this.getScript().getACommand() |
      poisonableLocalScriptsDataModel(regexp, path_group) and
      not cmd.matches("%${{%") and
      path = trimQuotes(cmd.regexpCapture(regexp, path_group))
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
        trimQuotes(cmd.regexpCapture("(?i)^\\s*(source|sh|bash|zsh|fish)\\s+(\"[^\"]+\"|'[^']+'|(?:\\$\\{\\{[^\\r\\n]*?\\}\\}|[^\\s])+)",
            2))
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
        trimQuotes(cmd.regexpCapture("(?i)^\\s*(?:&\\s+|\\.\\s+)?(\"[^\"]+\\.ps1\"|'[^']+\\.ps1'|(?:\\.\\\\|\\./)[^\\s]+\\.ps1)\\s*$",
            1))
    )
  }

  string getRawPath() { result = path }

  string getPath() { result = getNormalizedPoisonablePath(getEffectiveScriptPath(this)) }
}

class LocalActionUsesStep extends PoisonableStep, UsesStep {
  LocalActionUsesStep() { this.getCallee().matches("./%") }

  string getPath() { result = getNormalizedPoisonablePath(this.getCallee()) }
}

private class PoisonablePathInput extends NormalizableFilepath {
  PoisonablePathInput() {
    exists(LocalScriptExecutionRunStep step | this = getEffectiveScriptPath(step) and this != "?")
    or
    exists(LocalActionUsesStep step |
      not hasUnresolvedActionsPathSyntax(step.getCallee()) and
      this = canonicalizeActionsPathSyntax(step.getCallee())
    )
  }
}

bindingset[run]
private string getAKnownWorkingDirectory(Run run) {
  result = run.getWorkingDirectory() and not hasUnresolvedActionsPathSyntax(result)
  or
  exists(string name |
    name =
      run.getWorkingDirectory()
          .trim()
          .regexpCapture("(?i)^\\$\\{\\{\\s*env\\.([A-Za-z_][A-Za-z0-9_]*)\\s*\\}\\}$", 1) and
    result = run.getInScopeEnvVarValue(name).getValue() and
    not hasUnresolvedActionsPathSyntax(result)
  )
}

bindingset[run]
private string getEffectiveWorkingDirectory(Run run) {
  result = getAKnownWorkingDirectory(run)
  or
  not exists(getAKnownWorkingDirectory(run)) and result = run.getWorkingDirectory()
}

bindingset[run, path]
private string mapKnownWorkspacePath(Run run, string path) {
  exists(string workspaceRoot |
    workspaceRoot =
      canonicalizeActionsPathSyntax(run.getInScopeEnvVarValue("GITHUB_WORKSPACE").getValue())
          .regexpReplaceAll("/$", "") and
    (workspaceRoot.matches("/%") or workspaceRoot.regexpMatch("^[A-Za-z]:/.*")) and
    (
      path = workspaceRoot and result = "GITHUB_WORKSPACE"
      or
      path.indexOf(workspaceRoot + "/") = 0 and
      result = "GITHUB_WORKSPACE" + path.substring(workspaceRoot.length(), path.length())
    )
  )
  or
  not exists(string workspaceRoot |
    workspaceRoot =
      canonicalizeActionsPathSyntax(run.getInScopeEnvVarValue("GITHUB_WORKSPACE").getValue())
          .regexpReplaceAll("/$", "") and
    (workspaceRoot.matches("/%") or workspaceRoot.regexpMatch("^[A-Za-z]:/.*")) and
    (path = workspaceRoot or path.indexOf(workspaceRoot + "/") = 0)
  ) and
  result = path
}

bindingset[step]
private string getEffectiveScriptPath(LocalScriptExecutionRunStep step) {
  exists(string rawPath, string workingDirectory |
    rawPath = step.getRawPath() and
    workingDirectory = getEffectiveWorkingDirectory(step) and
    (
      hasUnresolvedActionsPathSyntax(rawPath) and result = "?"
      or
      exists(string canonicalPath |
        not hasUnresolvedActionsPathSyntax(rawPath) and
        canonicalPath = canonicalizeActionsPathSyntax(rawPath) and
        (
          canonicalPath = "GITHUB_WORKSPACE" or
          canonicalPath.matches("GITHUB_WORKSPACE/%") or
          canonicalPath.matches("/%") or
          canonicalPath.regexpMatch("^[A-Za-z]:/.*") or
          canonicalPath.matches("~/%")
        ) and
        result = mapKnownWorkspacePath(step, canonicalPath)
      )
      or
      exists(string canonicalPath, string normalizedDirectory |
        not hasUnresolvedActionsPathSyntax(rawPath) and
        not hasUnresolvedActionsPathSyntax(workingDirectory) and
        canonicalPath = canonicalizeActionsPathSyntax(rawPath) and
        not canonicalPath = "GITHUB_WORKSPACE" and
        not canonicalPath.matches("GITHUB_WORKSPACE/%") and
        not canonicalPath.matches("/%") and
        not canonicalPath.regexpMatch("^[A-Za-z]:/.*") and
        not canonicalPath.matches("~/%") and
        normalizedDirectory =
          mapKnownWorkspacePath(step, normalizePath(workingDirectory)).regexpReplaceAll("/$", "") and
        result = normalizedDirectory + "/" + canonicalPath
      )
      or
      exists(string canonicalPath |
        not hasUnresolvedActionsPathSyntax(rawPath) and
        hasUnresolvedActionsPathSyntax(workingDirectory) and
        canonicalPath = canonicalizeActionsPathSyntax(rawPath) and
        not canonicalPath = "GITHUB_WORKSPACE" and
        not canonicalPath.matches("GITHUB_WORKSPACE/%") and
        not canonicalPath.matches("/%") and
        not canonicalPath.regexpMatch("^[A-Za-z]:/.*") and
        not canonicalPath.matches("~/%") and
        result = "?"
      )
    )
  )
}

bindingset[rawPath]
private string getNormalizedPoisonablePath(string rawPath) {
  rawPath = "?" and result = "?"
  or
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
