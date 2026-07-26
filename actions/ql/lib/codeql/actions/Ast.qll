private import codeql.actions.ast.internal.Ast
private import codeql.actions.ast.internal.ExpressionParser
private import codeql.Locations
import codeql.actions.Helper

class AstNode instanceof AstNodeImpl {
  AstNode getAChildNode() { result = super.getAChildNode() }

  AstNode getParentNode() { result = super.getParentNode() }

  string getAPrimaryQlClass() { result = super.getAPrimaryQlClass() }

  Location getLocation() { result = super.getLocation() }

  string toString() { result = super.toString() }

  Step getEnclosingStep() { result = super.getEnclosingStep() }

  Job getEnclosingJob() { result = super.getEnclosingJob() }

  Event getATriggerEvent() { result = super.getATriggerEvent() }

  Workflow getEnclosingWorkflow() { result = super.getEnclosingWorkflow() }

  CompositeAction getEnclosingCompositeAction() { result = super.getEnclosingCompositeAction() }

  Expression getInScopeEnvVarExpr(string name) { result = super.getInScopeEnvVarExpr(name) }

  ScalarValue getInScopeDefaultValue(string name, string prop) {
    result = super.getInScopeDefaultValue(name, prop)
  }
}

class ScalarValue extends AstNode instanceof ScalarValueImpl {
  string getValue() { result = super.getValue() }
}

class Expression extends AstNode instanceof ExpressionImpl {
  string expression;
  string rawExpression;

  Expression() {
    expression = this.getExpression() and
    rawExpression = this.getRawExpression()
  }

  string getExpression() { result = expression }

  string getRawExpression() { result = rawExpression }

  string getNormalizedExpression() { result = normalizeExpr(expression) }

  /** Gets the root of the parsed expression syntax tree, if parsing succeeds. */
  ExpressionRoot getRoot() { result.getExpression() = this }
}

/** A node in a parsed GitHub Actions expression syntax tree. */
abstract class ExpressionNode instanceof ExpressionNodeImpl {
  Expression getExpression() { result = super.getExpression() }

  ExpressionNode getAChild() { result = super.getAChild() }

  ExpressionNode getChild(int i) { result = super.getChild(i) }

  ExpressionNode getParent() { result = super.getParent() }

  string getKind() { result = super.getKind() }

  string getText() { result = super.getText() }

  int getStartOffset() { result = super.getStartOffset() }

  int getEndOffset() { result = super.getEndOffset() }

  /**
   * Holds if this node has the specified source span. For YAML scalars whose decoded value cannot
   * be mapped losslessly, this is the span of the containing scalar.
   */
  predicate hasSourceLocation(string path, int sl, int sc, int el, int ec) {
    super.hasLocationInfo(path, sl, sc, el, ec)
  }

  /** Holds if this node's source span is exact rather than a containing scalar span. */
  predicate hasExactSourceLocation() { super.hasExactSourceLocation() }

  string getSourceFilePath() { this.hasSourceLocation(result, _, _, _, _) }

  int getSourceStartLine() { this.hasSourceLocation(_, result, _, _, _) }

  int getSourceStartColumn() { this.hasSourceLocation(_, _, result, _, _) }

  int getSourceEndLine() { this.hasSourceLocation(_, _, _, result, _) }

  int getSourceEndColumn() { this.hasSourceLocation(_, _, _, _, result) }

  string toString() { result = super.toString() }
}

/** The root of a parsed GitHub Actions expression. */
class ExpressionRoot extends ExpressionNode instanceof ExpressionRootImpl { }

/** A binary operation in a GitHub Actions expression. */
class BinaryExpression extends ExpressionNode instanceof BinaryExpressionImpl {
  ExpressionNode getLeftOperand() { result = super.getLeftOperand() }

  ExpressionNode getRightOperand() { result = super.getRightOperand() }

  string getOperator() { result = super.getOperator() }
}

/** A unary operation in a GitHub Actions expression. */
class UnaryExpression extends ExpressionNode instanceof UnaryExpressionImpl {
  ExpressionNode getOperand() { result = super.getOperand() }

  string getOperator() { result = super.getOperator() }
}

/** An identifier in a GitHub Actions expression. */
class IdentifierExpression extends ExpressionNode instanceof IdentifierExpressionImpl {
  string getName() { result = super.getName() }
}

/** A function call in a GitHub Actions expression. */
class FunctionCallExpression extends ExpressionNode instanceof FunctionCallExpressionImpl {
  IdentifierExpression getCallee() { result = super.getCallee() }

  ExpressionNode getArgument(int i) { result = super.getArgument(i) }
}

/** A property, wildcard, or index access in a GitHub Actions expression. */
class AccessExpression extends ExpressionNode instanceof AccessExpressionImpl {
  ExpressionNode getBase() { result = super.getBase() }

  ExpressionNode getAccessor() { result = super.getAccessor() }

  string getAccessPath() { result = normalizeExpr(this.getText()) }
}

/** A named property accessor in a GitHub Actions expression. */
class PropertyAccessExpression extends ExpressionNode instanceof PropertyAccessExpressionImpl {
  string getName() { result = super.getName() }
}

/** A wildcard property accessor in a GitHub Actions expression. */
class WildcardAccessExpression extends ExpressionNode instanceof WildcardAccessExpressionImpl { }

/** An index accessor in a GitHub Actions expression. */
class IndexAccessExpression extends ExpressionNode instanceof IndexAccessExpressionImpl {
  ExpressionNode getIndex() { result = super.getIndex() }
}

/** A Boolean, null, number, or string literal in a GitHub Actions expression. */
class LiteralExpression extends ExpressionNode instanceof LiteralExpressionImpl {
  string getValue() { result = super.getValue() }
}

/** An `env` in workflow, job or step. */
class Env extends AstNode instanceof EnvImpl {
  /** Gets an environment variable value given its name. */
  ScalarValueImpl getEnvVarValue(string name) { result = super.getEnvVarValue(name) }

  /** Gets an environment variable value. */
  ScalarValueImpl getAnEnvVarValue() { result = super.getAnEnvVarValue() }

  /** Gets an environment variable expressin given its name. */
  ExpressionImpl getEnvVarExpr(string name) { result = super.getEnvVarExpr(name) }

  /** Gets an environment variable expression. */
  ExpressionImpl getAnEnvVarExpr() { result = super.getAnEnvVarExpr() }
}

/**
 * A custom composite action. This is a mapping at the top level of an Actions YAML action file.
 * See https://docs.github.com/en/actions/creating-actions/metadata-syntax-for-github-actions.
 */
class CompositeAction extends AstNode instanceof CompositeActionImpl {
  Runs getRuns() { result = super.getRuns() }

  Outputs getOutputs() { result = super.getOutputs() }

  Expression getAnOutputExpr() { result = super.getAnOutputExpr() }

  Expression getOutputExpr(string outputName) { result = super.getOutputExpr(outputName) }

  Input getAnInput() { result = super.getAnInput() }

  Input getInput(string inputName) { result = super.getInput(inputName) }

  LocalJob getACallerJob() { result = super.getACallerJob() }

  UsesStep getACallerStep() { result = super.getACallerStep() }

  predicate isPrivileged() { super.isPrivileged() }
}

/**
 * An Actions workflow. This is a mapping at the top level of an Actions YAML workflow file.
 * See https://docs.github.com/en/actions/reference/workflow-syntax-for-github-actions.
 */
class Workflow extends AstNode instanceof WorkflowImpl {
  Env getEnv() { result = super.getEnv() }

  string getName() { result = super.getName() }

  Job getAJob() { result = super.getAJob() }

  Job getJob(string jobId) { result = super.getJob(jobId) }

  Permissions getPermissions() { result = super.getPermissions() }

  Strategy getStrategy() { result = super.getStrategy() }

  On getOn() { result = super.getOn() }
}

class ReusableWorkflow extends Workflow instanceof ReusableWorkflowImpl {
  Outputs getOutputs() { result = super.getOutputs() }

  Expression getAnOutputExpr() { result = super.getAnOutputExpr() }

  Expression getOutputExpr(string outputName) { result = super.getOutputExpr(outputName) }

  Input getAnInput() { result = super.getAnInput() }

  Input getInput(string inputName) { result = super.getInput(inputName) }

  string getASecretName() { result = super.getASecretName() }

  predicate declaresSecret(string secretName) { super.declaresSecret(secretName) }

  predicate isSecretRequired(string secretName) { super.isSecretRequired(secretName) }

  SecretsExpression getASecretExpr() { result = super.getASecretExpr() }

  ExternalJob getACaller() { result = super.getACaller() }
}

class Input extends AstNode instanceof InputImpl { }

class Default extends AstNode instanceof DefaultsImpl {
  ScalarValue getValue(string name, string prop) { result = super.getValue(name, prop) }
}

class Outputs extends AstNode instanceof OutputsImpl {
  string getAnOutputName() { result = super.getAnOutputName() }

  Expression getAnOutputExpr() { result = super.getAnOutputExpr() }

  Expression getOutputExpr(string outputName) { result = super.getOutputExpr(outputName) }

  string getOutputValue(string outputName) { result = super.getOutputValue(outputName) }

  override string toString() { result = "Job outputs node" }
}

class Permissions extends AstNode instanceof PermissionsImpl {
  /** Gets a supported `GITHUB_TOKEN` permission scope. */
  string getAScope() { result = super.getAScope() }

  bindingset[perm]
  string getPermission(string perm) { result = super.getPermission(perm) }

  /** Gets the configured value for `scope`, treating omitted mapping entries as `none`. */
  bindingset[scope]
  pragma[inline_late]
  string getConfiguredPermission(string scope) {
    result = super.getConfiguredPermission(scope)
  }

  string getAPermission() { result = super.getAPermission() }
}

class Strategy extends AstNode instanceof StrategyImpl {
  predicate hasMatrix() { super.hasMatrix() }

  string getAMatrixDimensionName() { result = super.getAMatrixDimensionName() }

  int getMatrixDimensionValueCount(string name) {
    result = super.getMatrixDimensionValueCount(name)
  }

  string getMatrixDimensionValue(string name, int index) {
    result = super.getMatrixDimensionValue(name, index)
  }

  predicate hasStaticCartesianMatrix() { super.hasStaticCartesianMatrix() }

  Expression getMatrixVarExpr(string varName) { result = super.getMatrixVarExpr(varName) }

  Expression getAMatrixVarExpr() { result = super.getAMatrixVarExpr() }
}

/**
 * https://docs.github.com/en/actions/using-workflows/workflow-syntax-for-github-actions#jobsjob_idneeds
 */
class Needs extends AstNode instanceof NeedsImpl {
  Job getANeededJob() { result = super.getANeededJob() }
}

class On extends AstNode instanceof OnImpl {
  Event getAnEvent() { result = super.getAnEvent() }
}

class Event extends AstNode instanceof EventImpl {
  string getName() { result = super.getName() }

  string getAnActivityType() { result = super.getAnActivityType() }

  string getAPropertyValue(string prop) { result = super.getAPropertyValue(prop) }

  predicate hasProperty(string prop) { super.hasProperty(prop) }

  predicate isExternallyTriggerable() { super.isExternallyTriggerable() }

  predicate isPrivileged() { super.isPrivileged() }
}

/**
 * An Actions job within a workflow.
 * See https://docs.github.com/en/actions/reference/workflow-syntax-for-github-actions#jobs.
 */
abstract class Job extends AstNode instanceof JobImpl {
  string getId() { result = super.getId() }

  Workflow getWorkflow() { result = super.getWorkflow() }

  Job getANeededJob() { result = super.getANeededJob() }

  Outputs getOutputs() { result = super.getOutputs() }

  Expression getAnOutputExpr() { result = super.getAnOutputExpr() }

  Expression getOutputExpr(string outputName) { result = super.getOutputExpr(outputName) }

  Env getEnv() { result = super.getEnv() }

  If getIf() { result = super.getIf() }

  string getContinueOnErrorValue() { result = super.getContinueOnErrorValue() }

  Expression getContinueOnErrorExpr() { result = super.getContinueOnErrorExpr() }

  Environment getEnvironment() { result = super.getEnvironment() }

  Permissions getPermissions() { result = super.getPermissions() }

  /**
    * Gets a statically possible permission for `scope` after applying workflow, job, and
    * reusable-workflow caller restrictions. Multiple results may exist for multiple callers or
    * trigger paths. Top-level jobs have no result when repository defaults are required, while a
    * reusable-workflow job may still have a conservative upper bound when a caller default is
    * unknown.
   */
  bindingset[scope]
  pragma[inline_late]
  string getEffectivePermission(string scope) { result = super.getEffectivePermission(scope) }

  Strategy getStrategy() { result = super.getStrategy() }

  string getARunsOnLabel() { result = super.getARunsOnLabel() }

  /** Gets the expression that selects this job's container image. */
  Expression getJobContainerImageExpr() { result = super.getJobContainerImageExpr() }

  /** Gets an expression that selects one of this job's service container images. */
  Expression getAServiceContainerImageExpr() { result = super.getAServiceContainerImageExpr() }

  /** Gets the configured registry username associated with `image`. */
  ScalarValue getRegistryUsernameForContainerImage(Expression image) {
    result = super.getRegistryUsernameForContainerImage(image)
  }

  /** Gets the registry password expression associated with `image`. */
  Expression getRegistryPasswordExprForContainerImage(Expression image) {
    result = super.getRegistryPasswordExprForContainerImage(image)
  }

  predicate isPrivileged() { super.isPrivileged() }

  predicate isPrivilegedExternallyTriggerable(Event event) {
    super.isPrivilegedExternallyTriggerable(event)
  }
}

abstract class StepsContainer extends AstNode instanceof StepsContainerImpl {
  Step getAStep() { result = super.getAStep() }

  /** Gets any directly or transitively contained step. */
  Step getAContainedStep() { result = super.getAContainedStep() }

  Step getStep(int i) { result = super.getStep(i) }
}

/**
 * An `runs` mapping in a custom composite action YAML.
 * See https://docs.github.com/en/actions/creating-actions/metadata-syntax-for-github-actions#runs
 */
class Runs extends StepsContainer instanceof RunsImpl {
  CompositeAction getAction() { result = super.getAction() }
}

/**
 * An Actions job within a workflow which is composed of steps.
 * See https://docs.github.com/en/actions/reference/workflow-syntax-for-github-actions#jobs.
 */
class LocalJob extends Job, StepsContainer instanceof LocalJobImpl { }

/**
 * A step within an Actions job.
 * See https://docs.github.com/en/actions/reference/workflow-syntax-for-github-actions#jobsjob_idsteps.
 */
class Step extends AstNode instanceof StepImpl {
  string getId() { result = super.getId() }

  Env getEnv() { result = super.getEnv() }

  If getIf() { result = super.getIf() }

  string getContinueOnErrorValue() { result = super.getContinueOnErrorValue() }

  Expression getContinueOnErrorExpr() { result = super.getContinueOnErrorExpr() }

  predicate runsInBackground() { super.runsInBackground() }

  /** Holds if this step may execute synchronously on the foreground path. */
  predicate mayRunInForeground() { super.mayRunInForeground() }

  StepsContainer getContainer() { result = super.getContainer() }

  Step getNextStep() { result = super.getNextStep() }

  Step getAFollowingStep() { result = super.getAFollowingStep() }
}

/** A run or action step launched asynchronously with `background: true`. */
class BackgroundStep extends Step instanceof BackgroundStepImpl {
  BackgroundCompletion getCompletion() { result = super.getCompletion() }

  Step getBarrier() { result = super.getBarrier() }
}

/** The completion point of an asynchronously running background step. */
class BackgroundCompletion extends AstNode instanceof BackgroundCompletionImpl {
  BackgroundStep getBackgroundStep() { result = super.getBackgroundStep() }
}

/** A barrier that waits for one or more named background steps. */
class WaitStep extends Step instanceof WaitStepImpl {
  string getATargetId() { result = super.getATargetId() }

  BackgroundStep getATargetStep() { result = super.getATargetStep() }
}

/** A barrier that waits for all active preceding background steps. */
class WaitAllStep extends Step instanceof WaitAllStepImpl {
  BackgroundStep getATargetStep() { result = super.getATargetStep() }
}

/** A step that cancels a named preceding background step. */
class CancelStep extends Step instanceof CancelStepImpl {
  string getTargetId() { result = super.getTargetId() }

  BackgroundStep getTargetStep() { result = super.getTargetStep() }
}

/** A group of run or action steps that execute concurrently and then join. */
class ParallelStep extends Step, StepsContainer instanceof ParallelStepImpl { }

/**
 * An If node representing a conditional statement.
 */
class If extends AstNode instanceof IfImpl {
  string getCondition() { result = super.getCondition() }

  Expression getConditionExpr() { result = super.getConditionExpr() }

  string getConditionStyle() { result = super.getConditionStyle() }
}

/**
 * An Environment node representing a deployment environment.
 */
class Environment extends AstNode instanceof EnvironmentImpl {
  string getName() { result = super.getName() }

  Expression getNameExpr() { result = super.getNameExpr() }

  string getUrl() { result = super.getUrl() }

  Expression getUrlExpr() { result = super.getUrlExpr() }

  string getDeploymentValue() { result = super.getDeploymentValue() }

  Expression getDeploymentExpr() { result = super.getDeploymentExpr() }
}

abstract class Uses extends AstNode instanceof UsesImpl {
  string getCallee() { result = super.getCallee() }

  ScalarValue getCalleeNode() { result = super.getCalleeNode() }

  /** Holds if this call uses a remote reference rather than a local path. */
  predicate isRemoteCall() { super.isRemoteCall() }

  string getVersion() { result = super.getVersion() }

  int getMajorVersion() { result = super.getMajorVersion() }

  string getArgument(string argName) { result = super.getArgument(argName) }

  Expression getArgumentExpr(string argName) { result = super.getArgumentExpr(argName) }
}

class UsesStep extends Step, Uses instanceof UsesStepImpl { }

class ExternalJob extends Job, Uses instanceof ExternalJobImpl {
  string getSecret(string secretName) { result = super.getSecret(secretName) }

  Expression getASecretExpr() { result = super.getASecretExpr() }

  Expression getSecretExpr(string secretName) { result = super.getSecretExpr(secretName) }

  predicate inheritsSecrets() { super.inheritsSecrets() }
}

/**
 * A `run` field within an Actions job step, which runs command-line programs using an operating system shell.
 * See https://docs.github.com/en/free-pro-team@latest/actions/reference/workflow-syntax-for-github-actions#jobsjob_idstepsrun.
 */
class Run extends Step instanceof RunImpl {
  ShellScript getScript() { result = super.getScript() }

  Expression getAnScriptExpr() { result = super.getAnScriptExpr() }

  string getWorkingDirectory() { result = super.getWorkingDirectory() }

  string getShell() { result = super.getShell() }
}

class ShellScript extends ScalarValueImpl instanceof ShellScriptImpl {
  string getRawScript() { result = super.getRawScript() }

  string getStmt(int i) { result = super.getStmt(i) }

  string getAStmt() { result = super.getAStmt() }

  string getCommand(int i) { result = super.getCommand(i) }

  string getACommand() { result = super.getACommand() }

  string getFileReadCommand(int i) { result = super.getFileReadCommand(i) }

  string getAFileReadCommand() { result = super.getAFileReadCommand() }

  predicate getAssignment(int i, string name, string data) { super.getAssignment(i, name, data) }

  predicate getAnAssignment(string name, string data) { super.getAnAssignment(name, data) }

  predicate getAWriteToGitHubEnv(string name, string data) {
    super.getAWriteToGitHubEnv(name, data)
  }

  predicate getAWriteToGitHubOutput(string name, string data) {
    super.getAWriteToGitHubOutput(name, data)
  }

  predicate getAWriteToGitHubPath(string data) { super.getAWriteToGitHubPath(data) }

  predicate getAnEnvReachingGitHubOutputWrite(string var, string output_field) {
    super.getAnEnvReachingGitHubOutputWrite(var, output_field)
  }

  predicate getACmdReachingGitHubOutputWrite(string cmd, string output_field) {
    super.getACmdReachingGitHubOutputWrite(cmd, output_field)
  }

  predicate getAnEnvReachingGitHubEnvWrite(string var, string output_field) {
    super.getAnEnvReachingGitHubEnvWrite(var, output_field)
  }

  predicate getACmdReachingGitHubEnvWrite(string cmd, string output_field) {
    super.getACmdReachingGitHubEnvWrite(cmd, output_field)
  }

  predicate getAnEnvReachingGitHubPathWrite(string var) {
    super.getAnEnvReachingGitHubPathWrite(var)
  }

  predicate getACmdReachingGitHubPathWrite(string cmd) { super.getACmdReachingGitHubPathWrite(cmd) }

  predicate getAnEnvReachingArgumentInjectionSink(string var, string command, string argument) {
    super.getAnEnvReachingArgumentInjectionSink(var, command, argument)
  }

  predicate getACmdReachingArgumentInjectionSink(string cmd, string command, string argument) {
    super.getACmdReachingArgumentInjectionSink(cmd, command, argument)
  }

  predicate fileToGitHubEnv(string path) { super.fileToGitHubEnv(path) }

  predicate fileToGitHubOutput(string path) { super.fileToGitHubOutput(path) }

  predicate fileToGitHubPath(string path) { super.fileToGitHubPath(path) }
}

abstract class SimpleReferenceExpression extends AstNode instanceof SimpleReferenceExpressionImpl {
  string getFieldName() { result = super.getFieldName() }

  AstNode getTarget() { result = super.getTarget() }
}

class JsonReferenceExpression extends AstNode instanceof JsonReferenceExpressionImpl {
  string getAccessPath() { result = super.getAccessPath() }

  string getInnerExpression() { result = super.getInnerExpression() }
}

class GitHubExpression extends SimpleReferenceExpression instanceof GitHubExpressionImpl { }

class SecretsExpression extends SimpleReferenceExpression instanceof SecretsExpressionImpl { }

class StepsExpression extends SimpleReferenceExpression instanceof StepsExpressionImpl {
  string getStepId() { result = super.getStepId() }
}

class NeedsExpression extends SimpleReferenceExpression instanceof NeedsExpressionImpl {
  string getNeededJobId() { result = super.getNeededJobId() }
}

class JobsExpression extends SimpleReferenceExpression instanceof JobsExpressionImpl { }

class InputsExpression extends SimpleReferenceExpression instanceof InputsExpressionImpl { }

class EnvExpression extends SimpleReferenceExpression instanceof EnvExpressionImpl { }

class MatrixExpression extends SimpleReferenceExpression instanceof MatrixExpressionImpl {
  /** Gets a scalar value declared for this matrix expression. */
  string getADeclaredValue() { result = super.getLiteralValues() }
}
