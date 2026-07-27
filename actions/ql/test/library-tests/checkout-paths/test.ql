import actions
import codeql.actions.security.PoisonableSteps
import codeql.actions.security.UntrustedCheckoutQuery

query predicate checkoutPaths(string stepId, string path) {
  exists(PRHeadCheckoutStep checkout |
    checkout.getId() = stepId and
    path = checkout.getPath()
  )
}

query predicate poisonablePaths(string stepId, string path) {
  exists(LocalScriptExecutionRunStep step |
    step.getId() = stepId and
    path = step.getPath()
  )
}

query predicate pathContainment(string candidate, string root) {
  candidate =
    [
      "GITHUB_WORKSPACE/candidate", "GITHUB_WORKSPACE/candidate/proof.sh",
      "GITHUB_WORKSPACE/a/b/proof.sh"
    ] and
  root = ["GITHUB_WORKSPACE/candidate", "GITHUB_WORKSPACE/candidate", "GITHUB_WORKSPACE/a/b"] and
  isSubpath(candidate, root)
}

query predicate pathNonContainment(string candidate, string root) {
  (
    candidate = "GITHUB_WORKSPACE/candidate-other/proof.sh" and
    root = "GITHUB_WORKSPACE/candidate"
    or
    candidate = "GITHUB_WORKSPACE/a/b-other/proof.sh" and root = "GITHUB_WORKSPACE/a/b"
    or
    candidate = "GITHUB_WORKSPACE/trusted.sh" and root = "GITHUB_WORKSPACE/candidate"
  ) and
  not isSubpath(candidate, root)
}
