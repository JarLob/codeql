/**
 * @name PATH environment variable built from user-controlled sources
 * @description Building the PATH environment variable from user-controlled sources may alter the execution of following system commands
 * @kind path-problem
 * @problem.severity error
 * @security-severity 9
 * @precision very-high
 * @id actions/envpath-injection/critical
 * @tags actions
 *       security
 *       external/cwe/cwe-077
 *       external/cwe/cwe-020
 */

import actions
import codeql.actions.security.EnvPathInjectionQuery
import EnvPathInjectionFlow::PathGraph
import codeql.actions.dataflow.FlowSources
import codeql.actions.security.ControlChecks

from EnvPathInjectionFlow::PathNode source, EnvPathInjectionFlow::PathNode sink, Event event
where
  exists(WorkflowExecutionContext context |
    EnvPathInjectionFlow::flowPath(source, sink) and
    source.getNode().(RemoteFlowSource).isUntrustedIn(context) and
    sinkMayExecuteForEvent(sink.getNode(), context.getEvent()) and
    (
      not source.getNode().(RemoteFlowSource).getSourceType() = "artifact" and
      context = getRelevantNonArtifactContextInPrivilegedContext(sink.getNode())
      or
      source.getNode().(RemoteFlowSource).getSourceType() = "artifact" and
      context = getRelevantArtifactContextInPrivilegedContext(sink.getNode())
    ) and
    event = context.getEvent()
  )
select sink.getNode(), source, sink,
  "Potential PATH environment variable injection in $@, which may be controlled by an external user ($@).",
  sink, sink.getNode().toString(), event, event.getName()
