/**
 * @name Code injection in pull request
 * @description Interpreting unsanitized user input as code allows a malicious user to perform arbitrary
 *              code execution in an isolated pull request workflow.
 * @kind path-problem
 * @problem.severity warning
 * @security-severity 3.0
 * @precision medium
 * @id actions/code-injection/low
 * @tags actions
 *       security
 *       external/cwe/cwe-094
 *       external/cwe/cwe-095
 *       external/cwe/cwe-116
 */

import actions
import codeql.actions.security.CodeInjectionQuery
import CodeInjectionFlow::PathGraph

from CodeInjectionFlow::PathNode source, CodeInjectionFlow::PathNode sink, Event event
where lowSeverityCodeInjection(source, sink, event)
select sink.getNode(), source, sink,
  "Potential code injection in $@ from ($@).", sink,
  sink.getNode().asExpr().(Expression).getRawExpression(), event, event.getName()
