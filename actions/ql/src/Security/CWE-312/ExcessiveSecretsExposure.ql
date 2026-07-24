/**
 * @name Excessive Secrets Exposure
 * @description All organization and repository secrets are passed to a workflow runner or reusable workflow.
 * @kind problem
 * @precision high
 * @security-severity 5.0
 * @problem.severity warning
 * @id actions/excessive-secrets-exposure
 * @tags actions
 *       security
 *       external/cwe/cwe-312
 */

import actions
import codeql.actions.ast.internal.Ast

private abstract class ExcessiveSecretExposure extends AstNode {
  abstract AstNode getReference();

  abstract string getValue();

  abstract string getMessage();
}

private class DynamicSecretsExpression extends ExcessiveSecretExposure, Expression {
  DynamicSecretsExpression() {
    getAToJsonReferenceExpression(this.getExpression(), _).matches("secrets%")
    or
    this.getExpression().matches("secrets[%") and
    not this.getExpression().matches("secrets[\"%") and
    not this.getExpression().matches("secrets['%")
  }

  override AstNode getReference() { result = this }

  override string getValue() { result = this.getExpression() }

  override string getMessage() {
    result = "All organization and repository secrets are passed to the workflow runner in $@"
  }
}

private class InheritedSecretsCall extends ExcessiveSecretExposure, ExternalJob {
  InheritedSecretsCall() { this.inheritsSecrets() }

  override AstNode getReference() { result = this.getCalleeNode() }

  override string getValue() { result = "secrets: inherit" }

  override string getMessage() {
    result = "All organization and repository secrets are passed to reusable workflow $@"
  }
}

from ExcessiveSecretExposure exposure
select exposure, exposure.getMessage(), exposure.getReference(), exposure.getValue()
