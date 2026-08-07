/**
 * @name Secret exfiltration
 * @description Secrets may be exfiltrated by an attacker who can control the data sent to an external service.
 * @kind path-problem
 * @problem.severity error
 * @security-severity 9.0
 * @precision high
 * @id actions/secret-exfiltration
 * @tags actions
 *       security
 *       experimental
 *       external/cwe/cwe-200
 */

import actions
import codeql.actions.security.SecretExfiltrationQuery
import SecretExfiltrationFlow::PathGraph

from SecretExfiltrationFlow::PathNode source, SecretExfiltrationFlow::PathNode sink
where
  SecretExfiltrationFlow::flowPath(source, sink) and
  (
    not isContextSensitiveSecretExfiltrationSink(sink.getNode()) and
    not exists(sink.getNode().asExpr().getEnclosingJob().getATriggerEvent())
    or
    exists(WorkflowExecutionContext context |
      source.getNode().(RemoteFlowSource).isUntrustedIn(context) and
      context.mayExecute(sink.getNode().asExpr()) and
      not context.isPullRequest() and
      (
        not isContextSensitiveSecretExfiltrationSink(sink.getNode())
        or
        context = getRelevantContextForSecretExfiltrationSink(sink.getNode()) and
        context.isPrivileged(sink.getNode().asExpr())
      )
    )
  )
select sink.getNode(), source, sink,
  "Potential secret exfiltration in $@, which may be leaked to an attacker-controlled resource.",
  sink, sink.getNode().asExpr().(Expression).getRawExpression()
