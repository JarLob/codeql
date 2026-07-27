private import codeql.actions.Ast
private import codeql.Locations
private import codeql.actions.security.ControlChecks
import codeql.actions.config.Config
import codeql.actions.Bash
import codeql.actions.PowerShell

bindingset[expr]
string normalizeExpr(string expr) {
  result =
    expr.regexpReplaceAll("\\['([a-zA-Z0-9_\\*\\-]+)'\\]", ".$1")
        .regexpReplaceAll("\\[\"([a-zA-Z0-9_\\*\\-]+)\"\\]", ".$1")
        .regexpReplaceAll("\\s*\\.\\s*", ".")
}

bindingset[regex]
string wrapRegexp(string regex) { result = "\\b" + regex + "\\b" }

bindingset[regex]
string wrapJsonRegexp(string regex) {
  result = ["fromJSON\\(\\s*" + regex + "\\s*\\)", "toJSON\\(\\s*" + regex + "\\s*\\)"]
}

bindingset[str]
string trimQuotes(string str) {
  result = str.trim().regexpReplaceAll("^(\"|')", "").regexpReplaceAll("(\"|')$", "")
}

/**
 * Canonicalizes path values derived from `github.run_id` or `github.run_attempt`. Both values are
 * stable for a workflow attempt: `github.run_id` remains unchanged across reruns, while
 * `github.run_attempt` changes only between attempts. Replacing them with `0` therefore allows
 * paths from the same attempt to be compared statically.
 *
 * Handles both a whole `format` expression and an expression embedded in a path:
 *
 * `${{ format('candidate-{0}/proof.sh', github.run_id) }}` -> `candidate-0/proof.sh`
 * `candidate-${{ github.run_attempt }}/proof.sh` -> `candidate-0/proof.sh`
 *
 * A literal `{0}` outside a recognized `format` expression remains unchanged:
 *
 * `literal-{0}/proof.sh` -> `literal-{0}/proof.sh`
 */
bindingset[path]
private string canonicalizeDeterministicRunPath(string path) {
  exists(string format |
    format =
      path.regexpCapture("(?i)^\\$\\{\\{\\s*format\\(\\s*'([A-Za-z0-9._/-]*\\{0\\}[A-Za-z0-9._/-]*)'\\s*,\\s*github\\.(run_id|run_attempt)\\s*\\)\\s*\\}\\}$",
        1) and
    result = format.replaceAll("{0}", "0")
  )
  or
  not path.regexpMatch("(?i)^\\$\\{\\{\\s*format\\(\\s*'([A-Za-z0-9._/-]*\\{0\\}[A-Za-z0-9._/-]*)'\\s*,\\s*github\\.(run_id|run_attempt)\\s*\\)\\s*\\}\\}$") and
  result = path.regexpReplaceAll("(?i)\\$\\{\\{\\s*github\\.(run_id|run_attempt)\\s*\\}\\}", "0")
}

/** Canonicalizes separators and statically known spellings of the Actions workspace. */
bindingset[path]
string canonicalizeActionsPathSyntax(string path) {
  result =
    canonicalizeDeterministicRunPath(trimQuotes(path)
          .replaceAll("\\", "/")
          .regexpReplaceAll("(?i)^\\$\\{\\{\\s*format\\(\\s*'\\{0\\}(/[^']*)?'\\s*,\\s*github\\.workspace\\s*\\)\\s*\\}\\}$",
            "GITHUB_WORKSPACE$1")
          .regexpReplaceAll("(?i)^\\$\\{\\{\\s*format\\(\\s*\"\\{0\\}(/[^\"]*)?\"\\s*,\\s*github\\.workspace\\s*\\)\\s*\\}\\}$",
            "GITHUB_WORKSPACE$1"))
        .regexpReplaceAll("(?i)^\\$\\{\\{\\s*(github\\.workspace|env\\.GITHUB_WORKSPACE)\\s*\\}\\}",
          "GITHUB_WORKSPACE")
        .regexpReplaceAll("(?i)^\\$env:GITHUB_WORKSPACE", "GITHUB_WORKSPACE")
        .regexpReplaceAll("^\\$\\{GITHUB_WORKSPACE\\}", "GITHUB_WORKSPACE")
        .regexpReplaceAll("^\\$GITHUB_WORKSPACE", "GITHUB_WORKSPACE")
        .regexpReplaceAll("(?i)^%GITHUB_WORKSPACE%", "GITHUB_WORKSPACE")
}

/** Holds if `path` still contains a variable or expression after canonicalization. */
bindingset[path]
predicate hasUnresolvedActionsPathSyntax(string path) {
  canonicalizeActionsPathSyntax(path)
      .regexpMatch(".*(\\$\\{\\{|\\$[A-Za-z_]|%[A-Za-z_][A-Za-z0-9_]*%).*")
}

predicate inPrivilegedContext(AstNode node, Event event) {
  node.getEnclosingJob().isPrivilegedExternallyTriggerable(event)
}

predicate inNonPrivilegedContext(AstNode node) {
  not node.getEnclosingJob().isPrivilegedExternallyTriggerable(_)
}

string defaultBranchNames() {
  repositoryDataModel(_, result)
  or
  not exists(string default_branch_name | repositoryDataModel(_, default_branch_name)) and
  result = ["main", "master"]
}

string getRepoRoot() {
  exists(Workflow w |
    w.getLocation().getFile().getRelativePath().indexOf("/.github/workflows") > 0 and
    result =
      w.getLocation()
          .getFile()
          .getRelativePath()
          .prefix(w.getLocation().getFile().getRelativePath().indexOf("/.github/workflows") + 1) and
    // exclude workflow_enum reusable workflows directory root
    not result.indexOf(".github/workflows/external/") > -1 and
    not result.indexOf(".github/actions/external/") > -1
    or
    not w.getLocation().getFile().getRelativePath().indexOf("/.github/workflows") > 0 and
    not w.getLocation().getFile().getRelativePath().indexOf(".github/workflows/external/") > -1 and
    not w.getLocation().getFile().getRelativePath().indexOf(".github/actions/external/") > -1 and
    result = ""
  )
}

bindingset[path]
string normalizePath(string path) {
  exists(string trimmed_path | trimmed_path = canonicalizeActionsPathSyntax(path) |
    // ./foo -> GITHUB_WORKSPACE/foo
    if trimmed_path.indexOf("./") = 0
    then result = trimmed_path.regexpReplaceAll("^\\./", "GITHUB_WORKSPACE/")
    else
      // GITHUB_WORKSPACE/foo -> GITHUB_WORKSPACE/foo
      if trimmed_path.indexOf("GITHUB_WORKSPACE/") = 0
      then result = trimmed_path
      else
        // foo -> GITHUB_WORKSPACE/foo
        if trimmed_path.regexpMatch("^[^$/~].*")
        then result = "GITHUB_WORKSPACE/" + trimmed_path.regexpReplaceAll("/$", "")
        else
          // ~/foo -> ~/foo
          // /foo -> /foo
          result = trimmed_path
  )
}

/**
 * Holds if the path cache_path is a subpath of the path untrusted_path.
 */
bindingset[subpath, path]
predicate isSubpath(string subpath, string path) {
  subpath = path
  or
  path.matches("%/") and subpath.indexOf(path) = 0
  or
  not path.matches("%/") and subpath.indexOf(path + "/") = 0
}
