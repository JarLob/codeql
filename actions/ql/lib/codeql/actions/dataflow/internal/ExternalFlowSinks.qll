private import actions
private import codeql.actions.DataFlow
private import codeql.actions.dataflow.internal.ExternalFlowExtensions as Extensions

predicate modeledSink(DataFlow::Node sink, string kind) {
  exists(Uses uses, string action, string version, string input |
    Extensions::actionsSinkModel(action, version, input, kind, _) and
    uses.getCallee() = action.toLowerCase() and
    (
      version.trim() = "*" and uses.getVersion() = any(string v)
      or
      version.trim() != "*" and uses.getVersion() = version.trim()
    ) and
    (
      input.trim().matches("env.%") and
      sink.asExpr() = uses.getInScopeEnvVarExpr(input.trim().replaceAll("env.", ""))
      or
      input.trim().matches("input.%") and
      sink.asExpr() = uses.getArgumentExpr(input.trim().replaceAll("input.", ""))
      or
      input.trim() = "artifact" and sink.asExpr() = uses
    )
  )
}