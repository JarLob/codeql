/**
 * @name Artifact poisoning
 * @description An attacker may be able to poison the workflow's artifacts and influence on consequent steps.
 * @kind path-problem
 * @problem.severity error
 * @precision very-high
 * @security-severity 9
 * @id actions/artifact-poisoning/critical
 * @tags actions
 *       security
 *       external/cwe/cwe-829
 */

import actions
import codeql.actions.security.ArtifactPoisoningQuery
import ArtifactPoisoningFlow::PathGraph
import codeql.actions.security.ControlChecks

from ArtifactPoisoningFlow::PathNode source, ArtifactPoisoningFlow::PathNode sink, Event event
where
  exists(WorkflowExecutionContext context |
    ArtifactPoisoningFlow::flowPath(source, sink) and
    source.getNode().(ArtifactSource).isUntrustedIn(context) and
    context = getRelevantContextInPrivilegedContext(sink.getNode()) and
    sinkMayExecuteForEvent(sink.getNode(), context.getEvent()) and
    event = context.getEvent()
  )
select source.getNode(), source, sink,
  "Potential artifact poisoning; the artifact being consumed has contents that may be controlled by an external user ($@).",
  event, event.getName()
