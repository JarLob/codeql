private import codeql.actions.ast.internal.Yaml
private import codeql.Locations
private import codeql.actions.Helper
private import codeql.actions.config.Config
private import codeql.actions.DataFlow

bindingset[text]
int numberOfLines(string text) { result = max(int i | exists(text.splitAt("\n", i))) }

/**
 * Gets the length of each line in the StringValue .
 */
bindingset[text]
int lineLength(string text, int i) { result = text.splitAt("\n", i).length() + 1 }

/**
 * Gets the sum of the length of the lines up to the given index.
 */
bindingset[text]
int partialLineLengthSum(string text, int i) {
  i in [0 .. numberOfLines(text)] and
  result = sum(int j, int length | j in [0 .. i] and length = lineLength(text, j) | length)
}

private YamlValue getEvaluatedAnchorValue(YamlNode node) {
  node instanceof YamlValue and result = node
  or
  node instanceof YamlAliasNode and
  result.getAnchor() = node.(YamlAliasNode).getTarget() and
  result.getDocument() = node.getDocument()
}

private YamlNode getAnExpandedYamlChild(YamlNode parent) {
  result = parent.getAChildNode()
  or
  parent instanceof YamlAliasNode and result = getEvaluatedAnchorValue(parent)
}

private YamlNode getRawMappingValue(YamlMapping mapping, string key) {
  exists(int index, YamlScalar keyNode |
    keyNode = mapping.getKeyNode(index) and
    keyNode.getValue() = key and
    result = mapping.getValueNode(index)
  )
}

private predicate getAJobOccurrence(
  YamlMapping workflow, YamlMapping job, YamlNode occurrence, string jobId
) {
  exists(YamlMapping jobs, int index, YamlScalar key |
    workflow instanceof YamlDocument and
    jobs = getEvaluatedAnchorValue(getRawMappingValue(workflow, "jobs")) and
    key = jobs.getKeyNode(index) and
    jobId = key.getValue() and
    occurrence = jobs.getValueNode(index) and
    job = getEvaluatedAnchorValue(occurrence)
  )
}

private YamlNode getAContainerOccurrence(YamlMapping container) {
  exists(YamlMapping workflow, string jobId |
    getAJobOccurrence(workflow, container, result, jobId)
  )
  or
  result = container
}

private predicate getAStepContainer(
  YamlMapping container, YamlNode containerOccurrence, string field
) {
  field = "steps" and containerOccurrence = getAContainerOccurrence(container)
  or
  field = "parallel" and
  getAStepOccurrence(container, _, containerOccurrence) and
  exists(getRawMappingValue(container, "parallel"))
}

private predicate getAStepOccurrence(
  YamlMapping step, YamlNode containerOccurrence, YamlNode elementOccurrence
) {
  exists(YamlMapping container, YamlSequence steps, string field, int index |
    getAStepContainer(container, containerOccurrence, field) and
    steps = getEvaluatedAnchorValue(getRawMappingValue(container, field)) and
    elementOccurrence = steps.getElementNode(index) and
    step = getEvaluatedAnchorValue(elementOccurrence)
  )
}

private newtype TAstOccurrence =
  MkAstOccurrence(YamlNode containerOccurrence, YamlNode elementOccurrence) {
    containerOccurrence = elementOccurrence
    or
    exists(YamlMapping step |
      getAStepOccurrence(step, containerOccurrence, elementOccurrence)
    )
  }

private class AstOccurrence extends TAstOccurrence {
  YamlNode containerOccurrence;
  YamlNode elementOccurrence;

  AstOccurrence() { this = MkAstOccurrence(containerOccurrence, elementOccurrence) }

  YamlNode getContainer() { result = containerOccurrence }

  YamlNode getElement() { result = elementOccurrence }

  string toString() { result = containerOccurrence + ":" + elementOccurrence }
}

bindingset[containerOccurrence, elementOccurrence]
private AstOccurrence getAstOccurrence(
  YamlNode containerOccurrence, YamlNode elementOccurrence
) {
  result.getContainer() = containerOccurrence and result.getElement() = elementOccurrence
}

private predicate hasAliasExpansion(
  YamlNode occurrenceRoot, YamlNode semanticRoot, YamlNode node
) {
  occurrenceRoot instanceof YamlAliasNode and node = getAnExpandedYamlChild*(semanticRoot)
  or
  exists(YamlAliasNode alias |
    alias = semanticRoot.getAChildNode*() and
    node = getAnExpandedYamlChild*(alias)
  )
}

private predicate hasStepAliasContext(
  YamlMapping step, YamlNode containerOccurrence, YamlNode elementOccurrence, YamlNode node
) {
  exists(YamlMapping container, string field |
    getAStepContainer(container, containerOccurrence, field) and
    getAStepOccurrence(step, containerOccurrence, elementOccurrence) and
    hasAliasExpansion(containerOccurrence, container, node)
  )
}

bindingset[node]
private predicate getAnAstContext(YamlNode node, AstOccurrence occurrence) {
  exists(YamlMapping step, YamlNode containerOccurrence, YamlNode elementOccurrence |
    getAStepOccurrence(step, containerOccurrence, elementOccurrence) and
    node = getAnExpandedYamlChild*(step) and
    hasStepAliasContext(step, containerOccurrence, elementOccurrence, node) and
    occurrence = MkAstOccurrence(containerOccurrence, elementOccurrence)
  )
  or
  exists(YamlMapping workflow, YamlMapping job, YamlNode jobOccurrence, string jobId |
    getAJobOccurrence(workflow, job, jobOccurrence, jobId) and
    node = getAnExpandedYamlChild*(job) and
    hasAliasExpansion(jobOccurrence, job, node) and
    not exists(YamlMapping step, YamlNode stepOccurrence |
      getAStepOccurrence(step, jobOccurrence, stepOccurrence) and
      node = getAnExpandedYamlChild*(step)
    ) and
    occurrence = MkAstOccurrence(jobOccurrence, jobOccurrence)
  )
  or
  occurrence = MkAstOccurrence(node, node)
}

string getADelimitedExpression(YamlString s, int offset) {
  // We use `regexpFind` to obtain *all* matches of `${{...}}`,
  // not just the last (greedy match) or first (reluctant match).
  result =
    s.getValue()
        .regexpFind("\\$\\{\\{(?:[^}]|}(?!}))*+\\}\\}", _, offset)
        .regexpCapture("(\\$\\{\\{(?:[^}]|}(?!}))*+\\}\\})", 1)
        .trim()
}

private newtype TAstNode =
  TExpressionNode(
    YamlNode key, YamlScalar value, string raw, int exprOffset, AstOccurrence occurrence
  ) {
    getAnAstContext(value, occurrence) and
    (
      raw = getADelimitedExpression(value, exprOffset) and
      exists(YamlMapping m |
        (
          exists(int i | value = m.getValueNode(i) and key = m.getKeyNode(i))
          or
          exists(int i |
            m.getValueNode(i).(YamlSequence).getElement(_) = value and key = m.getKeyNode(i)
          )
        )
      )
      or
      // `if`'s conditions do not need to be delimted with ${{}}
      exists(YamlMapping m |
        m.maps(key, value) and
        key.(YamlScalar).getValue() = ["if"] and
        value.getValue() = raw and
        exprOffset = 1
      )
    )
  } or
  TCompositeAction(YamlMapping n) {
    n instanceof YamlDocument and
    n.getFile().getBaseName() = ["action.yml", "action.yaml"] and
    n.lookup("runs").(YamlMapping).lookup("using").(YamlScalar).getValue() = "composite"
  } or
  TWorkflowNode(YamlMapping n) {
    n instanceof YamlDocument and
    n.lookup("jobs") instanceof YamlMapping
  } or
  TRunsNode(YamlMapping n) { exists(CompositeActionImpl a | a.getNode().lookup("runs") = n) } or
  TDefaultsNode(YamlMapping n) { exists(YamlMapping m | m.lookup("defaults") = n) } or
  TInputsNode(YamlMapping n) { exists(YamlMapping m | m.lookup("inputs") = n) } or
  TInputNode(YamlValue n) { exists(YamlMapping m | m.lookup("inputs").(YamlMapping).maps(n, _)) } or
  TOutputsNode(YamlMapping n) { exists(YamlMapping m | m.lookup("outputs") = n) } or
  TPermissionsNode(YamlMappingLikeNode n) { exists(YamlMapping m | m.lookup("permissions") = n) } or
  TStrategyNode(YamlMapping n) { exists(YamlMapping m | m.lookup("strategy") = n) } or
  TNeedsNode(YamlMappingLikeNode n) { exists(YamlMapping m | m.lookup("needs") = n) } or
  TJobNode(YamlMapping n, YamlNode occurrence, string jobId) {
    exists(YamlMapping workflow | getAJobOccurrence(workflow, n, occurrence, jobId))
  } or
  TOnNode(YamlMappingLikeNode n) { exists(YamlMapping w | w.lookup("on") = n) } or
  TEventNode(YamlScalar event, YamlMappingLikeNode n) {
    exists(OnImpl o |
      o.getNode().(YamlMapping).maps(event, n)
      or
      o.getNode().(YamlSequence).getElement(_) = event and event = n
      or
      o.getNode().(YamlScalar) = n and event = n
    )
  } or
  TStepNode(YamlMapping n, AstOccurrence occurrence) {
    exists(YamlNode containerOccurrence, YamlNode elementOccurrence |
      getAStepOccurrence(n, containerOccurrence, elementOccurrence) and
      occurrence = MkAstOccurrence(containerOccurrence, elementOccurrence)
    )
  } or
  TBackgroundCompletionNode(YamlMapping n, AstOccurrence occurrence) {
    exists(YamlNode containerOccurrence, YamlNode elementOccurrence |
      getAStepOccurrence(n, containerOccurrence, elementOccurrence) and
      occurrence = MkAstOccurrence(containerOccurrence, elementOccurrence)
    ) and
    n.lookup("background").(YamlScalar).getValue() = "true" and
    exists(n.lookup(["run", "uses"]))
  } or
  TIfNode(YamlValue n) { exists(YamlMapping m | m.lookup("if") = n) } or
  TEnvironmentNode(YamlValue n) { exists(YamlMapping m | m.lookup("environment") = n) } or
  TEnvNode(YamlMapping n) { exists(YamlMapping m | m.lookup("env") = n) } or
  TScalarValueNode(YamlScalar n, AstOccurrence occurrence) {
    getAnAstContext(n, occurrence) and
    exists(YamlMapping m | m.maps(_, n) or m.lookup(_).(YamlSequence).getElement(_) = n)
  }

abstract class AstNodeImpl extends TAstNode {
  abstract AstNodeImpl getAChildNode();

  abstract AstNodeImpl getParentNode();

  abstract string getAPrimaryQlClass();

  abstract Location getLocation();

  abstract YamlNode getNode();

  abstract string toString();

  /**
   * Gets the enclosing Job.
   */
  JobImpl getEnclosingJob() {
    result = this or
    result = this.getParentNode().getEnclosingJob() or
    result = this.(CompositeActionImpl).getACallerJob()
  }

  /**
   * Gets and Event triggering this node.
   */
  EventImpl getATriggerEvent() { result = this.getParentNode().getATriggerEvent() }

  /**
   * Gets the enclosing Step.
   */
  StepImpl getEnclosingStep() {
    this instanceof StepImpl and
    result = this
    or
    this instanceof ScalarValueImpl and
    result.getAChildNode*() = this.getParentNode()
  }

  /**
   * Gets the enclosing workflow if any.
   */
  WorkflowImpl getEnclosingWorkflow() {
    result = this or
    result = this.getParentNode().getEnclosingWorkflow()
  }

  /**
   * Gets the enclosing composite action if any.
   */
  CompositeActionImpl getEnclosingCompositeAction() {
    result = this or
    result = this.getParentNode().getEnclosingCompositeAction()
  }

  /**
   * Gets a environment variable expression by name in the scope of the current node.
   */
  ExpressionImpl getInScopeEnvVarExpr(string name) {
    exists(EnvImpl env |
      env.getNode().maps(any(YamlScalar s | s.getValue() = name), result.getParentNode().getNode()) and
      env.getParentNode().getAChildNode*() = this
    )
  }

  ScalarValueImpl getInScopeDefaultValue(string name, string prop) {
    exists(DefaultsImpl dft |
      this.getEnclosingJob().getNode().(YamlMapping).maps(_, dft.getNode()) and
      result = dft.getValue(name, prop)
    )
    or
    not exists(DefaultsImpl dft | this.getEnclosingJob() = dft.getParentNode()) and
    exists(DefaultsImpl dft |
      this.getEnclosingWorkflow().getNode().(YamlMapping).maps(_, dft.getNode()) and
      result = dft.getValue(name, prop)
    )
  }
}

bindingset[occurrence]
private StepImpl getStepAtOccurrence(AstOccurrence occurrence) {
  result.getOccurrence() = occurrence
}

bindingset[occurrence]
private JobImpl getJobAtOccurrence(YamlNode occurrence) { result.getOccurrence() = occurrence }

class ScalarValueImpl extends AstNodeImpl, TScalarValueNode {
  YamlScalar value;
  AstOccurrence occurrence;

  ScalarValueImpl() { this = TScalarValueNode(value, occurrence) }

  override string toString() { result = value.getValue() }

  override ExpressionImpl getAChildNode() { result.getParentNode() = this }

  override AstNodeImpl getParentNode() {
    exists(StepImpl step |
      step = getStepAtOccurrence(occurrence) and
      value = getAnExpandedYamlChild*(step.getNode()) and
      result = step
    )
    or
    not exists(YamlMapping step |
      getAStepOccurrence(step, occurrence.getContainer(), occurrence.getElement()) and
      value = getAnExpandedYamlChild*(step)
    ) and
    exists(AstNodeImpl n | n.getAChildNode() = this and result = n)
  }

  override string getAPrimaryQlClass() { result = "ScalarValueImpl" }

  override Location getLocation() { result = value.getLocation() }

  override YamlScalar getNode() { result = value }

  string getValue() { result = value.getValue() }

  AstOccurrence getOccurrence() { result = occurrence }

  YamlNode getContainerOccurrence() { result = occurrence.getContainer() }

  YamlNode getElementOccurrence() { result = occurrence.getElement() }

  override JobImpl getEnclosingJob() {
    result = getJobAtOccurrence(occurrence.getContainer())
    or
    exists(StepImpl step |
      step = getStepAtOccurrence(occurrence) and
      result = step.getEnclosingJob()
    )
    or
    occurrence = MkAstOccurrence(value, value) and result = super.getEnclosingJob()
  }

  override WorkflowImpl getEnclosingWorkflow() {
    result = this.getEnclosingJob().getWorkflow()
    or
    occurrence = MkAstOccurrence(value, value) and result = super.getEnclosingWorkflow()
  }

  override StepImpl getEnclosingStep() { result = getStepAtOccurrence(occurrence) }
}

bindingset[value, occurrence]
private ScalarValueImpl getScalarAtOccurrence(YamlScalar value, AstOccurrence occurrence) {
  result.getNode() = value and result.getOccurrence() = occurrence
}

bindingset[value, occurrence]
private ExpressionImpl getExpressionAtOccurrence(YamlScalar value, AstOccurrence occurrence) {
  result = TExpressionNode(_, value, _, _, occurrence)
}

class ShellScriptImpl extends ScalarValueImpl {
  ShellScriptImpl() { exists(YamlMapping run | run.lookup("run").(YamlScalar) = this.getNode()) }

  string getRawScript() { result = this.getValue().regexpReplaceAll("\\\\\\s*\n", "") }

  RunImpl getEnclosingRun() {
    result.getNode().lookup("run") = this.getNode() and
    result = getStepAtOccurrence(this.getOccurrence())
  }

  abstract string getStmt(int i);

  abstract string getAStmt();

  abstract string getCommand(int i);

  string getACommand() {
    if this.getEnclosingRun().getShell().matches("bash%")
    then result = this.(BashShellScript).getACommand()
    else
      if this.getEnclosingRun().getShell().matches("pwsh%")
      then result = this.(PowerShellScript).getACommand()
      else result = "NOT IMPLEMENTED"
  }

  abstract string getFileReadCommand(int i);

  abstract string getAFileReadCommand();

  abstract predicate getAssignment(int i, string name, string data);

  abstract predicate getAnAssignment(string name, string data);

  abstract predicate getAWriteToGitHubEnv(string name, string data);

  abstract predicate getAWriteToGitHubOutput(string name, string data);

  abstract predicate getAWriteToGitHubPath(string data);

  abstract predicate getAnEnvReachingGitHubOutputWrite(string var, string output_field);

  abstract predicate getACmdReachingGitHubOutputWrite(string cmd, string output_field);

  abstract predicate getAnEnvReachingGitHubEnvWrite(string var, string output_field);

  abstract predicate getACmdReachingGitHubEnvWrite(string cmd, string output_field);

  abstract predicate getAnEnvReachingGitHubPathWrite(string var);

  abstract predicate getACmdReachingGitHubPathWrite(string cmd);

  abstract predicate getAnEnvReachingArgumentInjectionSink(
    string var, string command, string argument
  );

  abstract predicate getACmdReachingArgumentInjectionSink(
    string cmd, string command, string argument
  );

  abstract predicate fileToGitHubEnv(string path);

  abstract predicate fileToGitHubOutput(string path);

  abstract predicate fileToGitHubPath(string path);
}

class ExpressionImpl extends AstNodeImpl, TExpressionNode {
  YamlNode key;
  YamlString value;
  string rawExpression;
  string fullExpression;
  int exprOffset;
  AstOccurrence occurrence;

  ExpressionImpl() {
    this = TExpressionNode(key, value, rawExpression, exprOffset - 1, occurrence) and
    exists(string trimmedExpression |
      trimmedExpression = rawExpression.trim() and
      if
        trimmedExpression.prefix(3) = "${{" and
        trimmedExpression.suffix(trimmedExpression.length() - 2) = "}}"
      then fullExpression = trimmedExpression.substring(3, trimmedExpression.length() - 2).trim()
      else fullExpression = trimmedExpression
    )
  }

  override string toString() { result = fullExpression }

  override AstNodeImpl getAChildNode() { none() }

  override ScalarValueImpl getParentNode() {
    result.getNode() = value and
    result.getOccurrence() = occurrence
  }

  override string getAPrimaryQlClass() { result = "ExpressionImpl" }

  override YamlNode getNode() { none() }

  AstOccurrence getOccurrence() { result = occurrence }

  YamlNode getContainerOccurrence() { result = occurrence.getContainer() }

  YamlNode getElementOccurrence() { result = occurrence.getElement() }

  override JobImpl getEnclosingJob() { result = this.getParentNode().getEnclosingJob() }

  override WorkflowImpl getEnclosingWorkflow() { result = this.getParentNode().getEnclosingWorkflow() }

  override StepImpl getEnclosingStep() { result = this.getParentNode().getEnclosingStep() }

  string getExpression() { result = fullExpression }

  string getFullExpression() { result = fullExpression }

  string getRawExpression() { result = rawExpression }

  /**
   * Gets the absolute coordinates of the expression.
   */
  predicate expressionLocation(int sl, int sc, int el, int ec) {
    exists(int lineDiff, string text, string style, Location loc |
      text = value.getValue() and
      loc = value.getLocation() and
      lineDiff = loc.getEndLine() - loc.getStartLine() and
      style = value.getStyle()
    |
      // eg:
      //  - run: echo "hello"
      //  - run: 'echo "hello"'
      //  - run: "echo 'hello'"
      style = ["", "\"", "'"] and
      lineDiff = 0 and
      sl = loc.getStartLine() and
      el = sl and
      (
        style = ["\"", "'"] and
        rawExpression = value.getValue() and
        sc = loc.getStartColumn() + exprOffset - 1
        or
        not style = ["\"", "'"] and sc = loc.getStartColumn() + exprOffset
        or
        not rawExpression = value.getValue() and sc = loc.getStartColumn() + exprOffset
      ) and
      ec = sc + rawExpression.length() - 1
      or
      // eg:
      //  - run: "echo 'hello'
      //      echo 'hello'"
      //  - run: "echo 'hello'
      //     echo 'hello'
      //     echo 'hello'"
      style = ["", "\"", "'"] and
      lineDiff > 0 and
      sl = loc.getStartLine() and
      el = loc.getEndLine() and
      sc = loc.getStartColumn() and
      ec = loc.getEndColumn()
      or
      // eg:
      //  - run: |
      //      echo "hello"
      //  - run: |
      //      echo "hello"
      //      echo "bye"
      style = "|" and
      exists(int r |
        (
          r > 0 and
          partialLineLengthSum(text, r - 1) < exprOffset and
          partialLineLengthSum(text, r) >= exprOffset and
          sl = loc.getStartLine() + r + 1 and
          el = sl and
          sc =
            key.getLocation().getStartColumn() + exprOffset - partialLineLengthSum(text, r - 1) + 2 -
              1 and
          ec = sc + rawExpression.length() - 1
          or
          r = 0 and
          partialLineLengthSum(text, r) > exprOffset and
          sl = loc.getStartLine() + r + 1 and
          el = sl and
          sc = key.getLocation().getStartColumn() + 2 + exprOffset and
          ec = sc + rawExpression.length() - 1
        )
      )
      or
      // eg:
      //  - run: >
      //      echo "hello"
      //  - run: >
      //      echo "hello"
      //      echo "hello"
      style = ">" and
      sl = loc.getStartLine() + 1 and
      el = loc.getEndLine() and
      sc = key.getLocation().getStartColumn() and
      ec = loc.getEndColumn()
    )
  }

  override Location getLocation() {
    exists(Location loc |
      this.hasLocationInfo(loc.getFile().getAbsolutePath(), loc.getStartLine(),
        loc.getStartColumn(), loc.getEndLine(), loc.getEndColumn()) and
      result = loc
    )
  }

  predicate hasLocationInfo(string path, int sl, int sc, int el, int ec) {
    path = value.getFile().getAbsolutePath() and
    this.expressionLocation(sl, sc, el, ec)
  }

  private predicate hasLosslessSingleLineSourceMapping() {
    exists(Location loc, string style |
      loc = value.getLocation() and
      style = value.getStyle() and
      loc.getStartLine() = loc.getEndLine() and
      (
        style = "" and
        loc.getEndColumn() - loc.getStartColumn() + 1 = value.getValue().length()
        or
        style = ["\"", "'"] and
        loc.getEndColumn() - loc.getStartColumn() + 1 = value.getValue().length() + 2
      )
    )
  }

  predicate expressionNodeLocationIsExact() { this.hasLosslessSingleLineSourceMapping() }

  bindingset[startOffset, endOffset]
  pragma[inline_late]
  predicate expressionNodeLocation(
    int startOffset, int endOffset, string path, int sl, int sc, int el, int ec
  ) {
    startOffset >= 0 and
    endOffset > startOffset and
    endOffset <= fullExpression.length() and
    this.hasLosslessSingleLineSourceMapping() and
    exists(int expressionStart, int expressionEnd, int expressionLine, int fullExpressionOffset |
      this.hasLocationInfo(path, expressionLine, expressionStart, expressionLine, expressionEnd) and
      fullExpressionOffset = rawExpression.indexOf(fullExpression)
    |
      sl = expressionLine and
      el = expressionLine and
      sc = expressionStart + fullExpressionOffset + startOffset and
      ec = expressionStart + fullExpressionOffset + endOffset - 1
    )
    or
    startOffset >= 0 and
    endOffset > startOffset and
    endOffset <= fullExpression.length() and
    not this.hasLosslessSingleLineSourceMapping() and
    exists(Location loc |
      loc = value.getLocation() and
      path = loc.getFile().getAbsolutePath()
    |
      sl = loc.getStartLine() and
      sc = loc.getStartColumn() and
      el = loc.getEndLine() and
      ec = loc.getEndColumn()
    )
  }
}

bindingset[owner, repo, action_path]
private string externalCompositeActionName(string owner, string repo, string action_path) {
  action_path.trim() = "" and result = owner.trim() + "/" + repo.trim()
  or
  not action_path.trim() = "" and
  result = owner.trim() + "/" + repo.trim() + "/" + action_path.trim()
}

class CompositeActionImpl extends AstNodeImpl, TCompositeAction {
  YamlMapping n;

  CompositeActionImpl() { this = TCompositeAction(n) }

  override string toString() { result = n.toString() }

  override AstNodeImpl getAChildNode() { result.getNode() = getAnExpandedYamlChild*(n) }

  override AstNodeImpl getParentNode() { none() }

  override string getAPrimaryQlClass() { result = "CompositeActionImpl" }

  override Location getLocation() { result = n.getLocation() }

  override YamlMapping getNode() { result = n }

  RunsImpl getRuns() { result.getNode() = n.lookup("runs") }

  OutputsImpl getOutputs() { result.getNode() = n.lookup("outputs") }

  ExpressionImpl getAnOutputExpr() { result = this.getOutputs().getAnOutputExpr() }

  ExpressionImpl getOutputExpr(string name) { result = this.getOutputs().getOutputExpr(name) }

  InputsImpl getInputs() { result.getNode() = n.lookup("inputs") }

  InputImpl getAnInput() { n.lookup("inputs").(YamlMapping).maps(result.getNode(), _) }

  InputImpl getInput(string name) {
    n.lookup("inputs").(YamlMapping).maps(result.getNode(), _) and
    result.getNode().getValue() = name
  }

  LocalJobImpl getACallerJob() { result = this.getACallerStep().getEnclosingJob() }

  UsesStepImpl getACallerStep() {
    exists(DataFlow::CallNode call |
      call.getCalleeNode() = this and
      result = call.getCfgNode().getAstNode()
    )
  }

  predicate getAnExternalCompositeActionModel(
    string owner, string repo, string action_path, string requested_ref,
    string resolved_commit_sha, string local_path
  ) {
    externalCompositeActionDataModel(owner, repo, action_path, requested_ref,
      resolved_commit_sha, local_path) and
    local_path.trim() = this.getLocation().getFile().getRelativePath()
  }

  predicate isExternalCompositeAction() {
    exists(string owner, string repo, string action_path, string requested_ref,
      string resolved_commit_sha, string local_path |
      this.getAnExternalCompositeActionModel(owner, repo, action_path, requested_ref,
        resolved_commit_sha, local_path)
    )
    or
    this.getLocation()
        .getFile()
        .getRelativePath()
        .matches("9466014afba34ef28239871ceabf4132/%")
  }

  string getResolvedPath() {
    exists(string owner, string repo, string action_path, string requested_ref,
      string resolved_commit_sha, string local_path |
      this.getAnExternalCompositeActionModel(owner, repo, action_path, requested_ref,
        resolved_commit_sha, local_path) and
      result =
        externalCompositeActionName(owner, repo, action_path) + "@" + requested_ref.trim()
    )
    or
    not this.isExternalCompositeAction() and
    result =
      ["", "./"] +
        this.getLocation()
            .getFile()
            .getRelativePath()
            .replaceAll(getRepoRoot(), "")
            .replaceAll("/action.yml", "")
            .replaceAll("/action.yaml", "")
  }

  private predicate hasExplicitSecretAccess() {
    // the job accesses a secret other than GITHUB_TOKEN
    exists(SecretsExpressionImpl expr |
      expr.getEnclosingCompositeAction() = this and not expr.getFieldName() = "GITHUB_TOKEN"
    )
  }

  /** Holds if the action is privileged. */
  predicate isPrivileged() {
    // the action explicitly accesses a secret
    this.hasExplicitSecretAccess()
    or
    // there is a privileged caller job
    (
      this.getACallerJob().isPrivileged()
      or
      not this.getACallerJob().isPrivileged() and
      not this.getACallerJob().hasKnownEffectivePermissions() and
      this.getACallerJob().getATriggerEvent().isPrivileged()
    )
  }

  override EventImpl getATriggerEvent() { result = this.getACallerJob().getATriggerEvent() }
}

class WorkflowImpl extends AstNodeImpl, TWorkflowNode {
  YamlMapping n;

  WorkflowImpl() { this = TWorkflowNode(n) }

  override string toString() { result = n.toString() }

  override AstNodeImpl getAChildNode() { result.getNode() = getAnExpandedYamlChild*(n) }

  override AstNodeImpl getParentNode() { none() }

  override string getAPrimaryQlClass() { result = "WorkflowImpl" }

  override Location getLocation() { result = n.getLocation() }

  override YamlMapping getNode() { result = n }

  override WorkflowImpl getEnclosingWorkflow() { result = this }

  /** Gets the `on` trigger events for this workflow. */
  OnImpl getOn() { result.getNode() = n.lookup("on") }

  /** Gets the 'global' `env` mapping in this workflow. */
  EnvImpl getEnv() { result.getNode() = n.lookup("env") }

  /** Gets the name of the workflow. */
  string getName() { result = n.lookup("name").(YamlString).getValue() }

  /** Gets the job within this workflow with the given job ID. */
  JobImpl getJob(string jobId) { result.getEnclosingWorkflow() = this and result.getId() = jobId }

  /** Gets a job within this workflow */
  JobImpl getAJob() { result.getEnclosingWorkflow() = this }

  /** Gets the permissions granted to this workflow. */
  PermissionsImpl getPermissions() { result.getNode() = n.lookup("permissions") }

  /** Gets the trigger event that starts this workflow. */
  override EventImpl getATriggerEvent() { this.getOn().getAnEvent() = result }

  /** Gets the strategy for this workflow. */
  StrategyImpl getStrategy() { result.getNode() = n.lookup("strategy") }
}

class ReusableWorkflowImpl extends AstNodeImpl, WorkflowImpl {
  YamlValue workflow_call;

  ReusableWorkflowImpl() {
    n.lookup("on").(YamlMappingLikeNode).getNode("workflow_call") = workflow_call
  }

  override AstNodeImpl getAChildNode() { result.getNode() = getAnExpandedYamlChild*(n) }

  override EventImpl getATriggerEvent() {
    // The trigger event for a reusable workflow is the trigger event of the caller workflow
    this.getACaller().getEnclosingWorkflow().getOn().getAnEvent() = result
    or
    // or the trigger event of the workflow if it has any other than workflow_call
    this.getOn().getAnEvent() = result and not result.getName() = "workflow_call"
  }

  OutputsImpl getOutputs() { result.getNode() = workflow_call.(YamlMapping).lookup("outputs") }

  ExpressionImpl getAnOutputExpr() { result = this.getOutputs().getAnOutputExpr() }

  ExpressionImpl getOutputExpr(string name) { result = this.getOutputs().getOutputExpr(name) }

  InputsImpl getInputs() { result.getNode() = workflow_call.(YamlMapping).lookup("inputs") }

  InputImpl getAnInput() {
    workflow_call.(YamlMapping).lookup("inputs").(YamlMapping).maps(result.getNode(), _)
  }

  InputImpl getInput(string name) {
    workflow_call.(YamlMapping).lookup("inputs").(YamlMapping).maps(result.getNode(), _) and
    result.getNode().(YamlString).getValue() = name
  }

  string getASecretName() {
    exists(YamlScalar key |
      workflow_call.(YamlMapping).lookup("secrets").(YamlMapping).maps(key, _) and
      result = key.getValue()
    )
  }

  predicate declaresSecret(string name) {
    exists(YamlValue secret |
      workflow_call.(YamlMapping).lookup("secrets").(YamlMapping).lookup(name) = secret
    )
  }

  predicate isSecretRequired(string name) {
    workflow_call
        .(YamlMapping)
        .lookup("secrets")
        .(YamlMapping)
        .lookup(name)
        .(YamlMapping)
        .lookup("required")
        .(YamlScalar)
        .getValue() = "true"
  }

  SecretsExpressionImpl getASecretExpr() {
    result.getEnclosingWorkflow() = this and this.declaresSecret(result.getFieldName())
  }

  ExternalJobImpl getACaller() {
    exists(DataFlow::CallNode call |
      call.getCalleeNode() = this and
      result = call.getCfgNode().getAstNode()
    )
  }

  predicate getAnExternalReusableWorkflowModel(
    string owner, string repo, string workflow_path, string requested_ref,
    string resolved_commit_sha, string local_path
  ) {
    externalReusableWorkflowDataModel(owner, repo, workflow_path, requested_ref,
      resolved_commit_sha, local_path) and
    local_path.trim() = this.getLocation().getFile().getRelativePath()
  }

  predicate isExternalReusableWorkflow() {
    exists(string owner, string repo, string workflow_path, string requested_ref,
      string resolved_commit_sha, string local_path |
      this.getAnExternalReusableWorkflowModel(owner, repo, workflow_path, requested_ref,
        resolved_commit_sha, local_path)
    )
    or
    this.getLocation()
        .getFile()
        .getRelativePath()
        .matches("9466014afba34ef28239871ceabf4132/%") // root folder for external workflows and composite actions
  }

  string getResolvedPath() {
    exists(string owner, string repo, string workflow_path, string requested_ref,
      string resolved_commit_sha, string local_path |
      this.getAnExternalReusableWorkflowModel(owner, repo, workflow_path, requested_ref,
        resolved_commit_sha, local_path) and
      result =
        owner.trim() + "/" + repo.trim() + "/" + workflow_path.trim() + "@" +
          requested_ref.trim()
    )
    or
    not this.isExternalReusableWorkflow() and
    result =
      ["", "./"] +
        this.getLocation()
            .getFile()
            .getRelativePath()
            .replaceAll(getRepoRoot(), "")
  }
}

class InputsImpl extends AstNodeImpl, TInputsNode {
  YamlMapping n;

  InputsImpl() { this = TInputsNode(n) }

  override string toString() { result = n.toString() }

  override AstNodeImpl getAChildNode() { result.getNode() = getAnExpandedYamlChild*(n) }

  //override AstNodeImpl getAChildNode() { result = this.getAnInput() }
  override AstNodeImpl getParentNode() { result.getAChildNode() = this }

  override string getAPrimaryQlClass() { result = "InputsImpl" }

  override Location getLocation() { result = n.getLocation() }

  override YamlMapping getNode() { result = n }

  InputImpl getAnInput() { n.maps(result.getNode(), _) }

  InputImpl getInput(string name) {
    n.maps(result.getNode(), _) and
    result.getNode().(YamlString).getValue() = name
  }
}

class DefaultsImpl extends AstNodeImpl, TDefaultsNode {
  YamlMapping n;

  DefaultsImpl() { this = TDefaultsNode(n) }

  override string toString() { result = n.toString() }

  override AstNodeImpl getAChildNode() { result.getNode() = getAnExpandedYamlChild*(n) }

  override AstNodeImpl getParentNode() { result.getAChildNode() = this }

  override string getAPrimaryQlClass() { result = "DefaultsImpl" }

  override Location getLocation() { result = n.getLocation() }

  override YamlMapping getNode() { result = n }

  ScalarValueImpl getValue(string name, string prop) {
    n.lookup(name).(YamlMapping).lookup(prop) = result.getNode()
  }
}

class InputImpl extends AstNodeImpl, TInputNode {
  YamlValue n;

  InputImpl() { this = TInputNode(n) }

  override string toString() { result = n.toString() }

  override AstNodeImpl getAChildNode() { result.getNode() = getAnExpandedYamlChild*(n) }

  override InputsImpl getParentNode() { result.getAChildNode() = this }

  override string getAPrimaryQlClass() { result = "InputImpl" }

  override Location getLocation() { result = n.getLocation() }

  override YamlScalar getNode() { result = n }
}

class OutputsImpl extends AstNodeImpl, TOutputsNode {
  YamlMapping n;

  OutputsImpl() { this = TOutputsNode(n) }

  override string toString() { result = n.toString() }

  override AstNodeImpl getAChildNode() { result.getNode() = getAnExpandedYamlChild*(n) }

  override AstNodeImpl getParentNode() { result.getAChildNode() = this }

  override string getAPrimaryQlClass() { result = "OutputsImpl" }

  override Location getLocation() { result = n.getLocation() }

  override YamlMapping getNode() { result = n }

  /** Gets an output expression. */
  ExpressionImpl getAnOutputExpr() { result = this.getOutputExpr(_) }

  /** Gets a specific output expression by name. */
  ExpressionImpl getOutputExpr(string name) {
    exists(YamlScalar l |
      l = result.getParentNode().getNode() and
      (
        n.lookup(name).(YamlMapping).lookup("value") = l or
        n.lookup(name) = l
      )
    )
  }

  /** Gets a specific output value by name. */
  string getOutputValue(string name) {
    result = n.lookup(name).(YamlMapping).lookup("value").(YamlString).getValue()
    or
    result = n.lookup(name).(YamlString).getValue()
  }

  string getAnOutputName() { n.maps(any(YamlString s | s.getValue() = result), _) }
}

private string permissionScope() {
  result =
    [
      "actions", "artifact-metadata", "attestations", "checks", "code-quality", "contents",
      "copilot-requests", "deployments", "discussions", "drives", "id-token", "issues",
      "models", "packages", "pages", "pull-requests", "repository-projects", "security-events",
      "statuses", "vulnerability-alerts"
    ]
}

private predicate isReadOnlyPermissionScope(string scope) {
  scope = ["models", "vulnerability-alerts"]
}

private predicate isWriteOnlyPermissionScope(string scope) {
  scope = ["copilot-requests", "id-token"]
}

bindingset[scope]
private string maximumPermission(string scope) {
  scope = permissionScope() and
  (
    isWriteOnlyPermissionScope(scope) and result = "none"
    or
    isReadOnlyPermissionScope(scope) and result = "read"
    or
    not isWriteOnlyPermissionScope(scope) and not isReadOnlyPermissionScope(scope) and
    result = "write"
  )
}

private int permissionLevel(string permission) {
  permission = "none" and result = 0
  or
  permission = "read" and result = 1
  or
  permission = "write" and result = 2
}

private string restrictPermission(string requested, string cap) {
  permissionLevel(requested) <= permissionLevel(cap) and result = requested
  or
  permissionLevel(cap) < permissionLevel(requested) and result = cap
}

class PermissionsImpl extends AstNodeImpl, TPermissionsNode {
  YamlMappingLikeNode n;

  PermissionsImpl() { this = TPermissionsNode(n) }

  override string toString() { result = n.toString() }

  override AstNodeImpl getAChildNode() { result.getNode() = getAnExpandedYamlChild*(n) }

  override AstNodeImpl getParentNode() { result.getAChildNode() = this }

  override string getAPrimaryQlClass() { result = "PermissionsImpl" }

  override Location getLocation() { result = n.getLocation() }

  override YamlMappingLikeNode getNode() { result = n }

  string getAScope() { result = permissionScope() }

  string getAPermission() {
    exists(YamlMapping mapping, YamlScalar scope, YamlScalar permission |
      mapping = n and
      mapping.maps(scope, permission) and
      result = scope.getValue() + ": " + permission.getValue()
    )
    or
    exists(YamlScalar scalar, string scope, string permission |
      scalar = n and
      scope = this.getAScope() and
      permission = this.getConfiguredPermission(scope) and
      not permission = "none" and
      (
        scalar.getValue() = "write-all"
        or
        scalar.getValue() = "read-all"
      ) and
      result = scope + ": " + permission
    )
  }

  bindingset[perm]
  string getPermission(string perm) {
    exists(string p |
      p = this.getAPermission() and p.matches(perm + ":%") and result = p.splitAt(":", 1).trim()
    )
  }

  bindingset[scope]
  pragma[inline_late]
  string getConfiguredPermission(string scope) {
    scope = this.getAScope() and
    (
      exists(YamlMapping mapping |
        mapping = n and
        (
          result = mapping.lookup(scope).(YamlScalar).getValue().trim().toLowerCase()
          or
          not exists(mapping.lookup(scope)) and result = "none"
        )
      )
      or
      exists(YamlScalar scalar |
        scalar = n and
        (
          scalar.getValue() = "read-all" and
          (
            isWriteOnlyPermissionScope(scope) and result = "none"
            or
            not isWriteOnlyPermissionScope(scope) and result = "read"
          )
          or
          scalar.getValue() = "write-all" and
          (
            isReadOnlyPermissionScope(scope) and result = "read"
            or
            not isReadOnlyPermissionScope(scope) and result = "write"
          )
        )
      )
    )
  }
}

class StrategyImpl extends AstNodeImpl, TStrategyNode {
  YamlMapping n;

  StrategyImpl() { this = TStrategyNode(n) }

  override string toString() { result = n.toString() }

  override AstNodeImpl getAChildNode() { result.getNode() = getAnExpandedYamlChild*(n) }

  override AstNodeImpl getParentNode() { result.getAChildNode() = this }

  override string getAPrimaryQlClass() { result = "StrategyImpl" }

  override Location getLocation() { result = n.getLocation() }

  override YamlMapping getNode() { result = n }

  YamlMapping getMatrix() { result = n.lookup("matrix") }

  predicate hasMatrix() { exists(n.lookup("matrix")) }

  string getAMatrixDimensionName() {
    exists(YamlScalar key |
      n.lookup("matrix").(YamlMapping).maps(key, _) and
      not key.getValue().toLowerCase() = ["include", "exclude"] and
      result = key.getValue()
    )
  }

  int getMatrixDimensionValueCount(string name) {
    name = this.getAMatrixDimensionName() and
    result = count(n.lookup("matrix").(YamlMapping).lookup(name).(YamlSequence).getElement(_))
  }

  string getMatrixDimensionValue(string name, int index) {
    name = this.getAMatrixDimensionName() and
    result =
      n.lookup("matrix")
          .(YamlMapping)
          .lookup(name)
          .(YamlSequence)
          .getElement(index)
          .(YamlScalar)
          .getValue()
  }

  predicate hasStaticCartesianMatrix() {
    exists(this.getAMatrixDimensionName()) and
    not exists(n.lookup("matrix").(YamlMapping).lookup(["include", "exclude"])) and
    forall(string name |
      name = this.getAMatrixDimensionName()
    |
      exists(n.lookup("matrix").(YamlMapping).lookup(name).(YamlSequence)) and
      this.getMatrixDimensionValueCount(name) > 0
    )
  }

  /** Holds if this strategy's effective matrix combinations are modeled exactly. */
  predicate hasExactMatrixCombinations() { hasBoundedMatrixCombinations(this) }

  /** Gets an effective matrix combination for this strategy. */
  MatrixCombinationImpl getAMatrixCombination() { result.getStrategy() = this }

  /** Gets an expression that can define the given matrix variable. */
  ExpressionImpl getMatrixVarExpr(string accessPath) {
    exists(MatrixAccessPathImpl p, ScalarValueImpl v |
      p.toString() = accessPath and
      (
        resolveMatrixAccessPath(n.lookup("matrix"), p).getNode(_) = v.getNode()
        or
        resolveMatrixAccessPath(
          this.getMatrix().lookup("include").(YamlSequence).getElementNode(_), p
        ).getNode(_) = v.getNode()
      ) and
      result.getParentNode() = v
    )
    or
    exists(MatrixAccessPathImpl p |
      p.toString() = accessPath and
      (
        result.getParentNode().getNode() = n.lookup("matrix")
        or
        result.getParentNode().getNode() =
          n.lookup("matrix").(YamlMapping).lookup("include")
      )
    )
  }

  /** Gets an expression used to define the matrix. */
  ExpressionImpl getAMatrixVarExpr() {
    n.lookup("matrix").getAChildNode*() = result.getParentNode().getNode()
  }
}

private int maxGeneratedMatrixCombinationCount() { result = 256 }

private int maxExactMatrixCombinationCount() { result = 16 }

bindingset[value]
pragma[inline_late]
private predicate isStaticMatrixScalar(YamlValue value) {
  value instanceof YamlScalar and
  not exists(ExpressionImpl expression | expression.getParentNode().getNode() = value)
}

private YamlValue getAMatrixValueChild(YamlValue parent) {
  parent instanceof YamlMapping and
  (
    result = parent.(YamlMapping).getKey(_)
    or
    result = parent.(YamlMapping).getValue(_)
  )
  or
  parent instanceof YamlSequence and result = parent.(YamlSequence).getElement(_)
}

bindingset[value]
pragma[inline_late]
private predicate isStaticMatrixValue(YamlValue value) {
  forall(YamlScalar scalar | scalar = getAMatrixValueChild*(value) |
    isStaticMatrixScalar(scalar)
  ) and
  forall(YamlMapping mapping, YamlValue key |
    mapping = getAMatrixValueChild*(value) and mapping.maps(key, _)
  |
    key instanceof YamlScalar
  )
}

bindingset[matrix, element]
pragma[inline_late]
private predicate isStaticMatrixDimensionElement(YamlMapping matrix, YamlValue element) {
  isStaticMatrixScalar(element)
  or
  not exists(matrix.lookup(["include", "exclude"])) and isStaticMatrixValue(element)
}

bindingset[entry]
pragma[inline_late]
private predicate isStaticMatrixControlEntry(YamlValue entry) {
  entry instanceof YamlMapping and
  forall(YamlValue key, YamlValue value | entry.(YamlMapping).maps(key, value) |
    key instanceof YamlScalar and isStaticMatrixScalar(value)
  )
}

bindingset[strategy]
pragma[inline_late]
private predicate hasStaticMatrixDefinition(StrategyImpl strategy) {
  exists(YamlMapping matrix |
    matrix = strategy.getMatrix() and
    not exists(YamlValue key, YamlValue value |
      matrix.maps(key, value) and
      not exists(YamlScalar scalarKey, YamlSequence sequence |
        scalarKey = key and
        sequence = value and
        (
          scalarKey.getValue().toLowerCase() = ["include", "exclude"] and
          not exists(YamlValue entry |
            entry = sequence.getElement(_) and not isStaticMatrixControlEntry(entry)
          )
          or
          not scalarKey.getValue().toLowerCase() = ["include", "exclude"] and
          not exists(YamlValue element |
            element = sequence.getElement(_) and
            not isStaticMatrixDimensionElement(matrix, element)
          )
        )
      )
    )
  )
}

private string getMatrixDimensionAt(StrategyImpl strategy, int index) {
  result =
    rank[index + 1](string name | name = strategy.getAMatrixDimensionName() |
      name order by name
    )
}

private int getBoundedMatrixProductPrefix(StrategyImpl strategy, int length) {
  length = 0 and result = 1
  or
  exists(int previous, string dimension |
    length > 0 and
    dimension = getMatrixDimensionAt(strategy, length - 1) and
    previous = getBoundedMatrixProductPrefix(strategy, length - 1) and
    result = previous * strategy.getMatrixDimensionValueCount(dimension) and
    result <= maxGeneratedMatrixCombinationCount()
  )
}

private int getBoundedBaseMatrixCombinationCount(StrategyImpl strategy) {
  not exists(strategy.getAMatrixDimensionName()) and result = 0
  or
  exists(strategy.getAMatrixDimensionName()) and
  result =
    getBoundedMatrixProductPrefix(strategy, count(strategy.getAMatrixDimensionName()))
}

private string getBaseMatrixAssignmentPrefix(StrategyImpl strategy, int length) {
  length = 0 and result = ""
  or
  exists(string prefix, string dimension, int valueIndex |
    length > 0 and
    dimension = getMatrixDimensionAt(strategy, length - 1) and
    valueIndex in [0 .. strategy.getMatrixDimensionValueCount(dimension) - 1] and
    prefix = getBaseMatrixAssignmentPrefix(strategy, length - 1) and
    (
      prefix = "" and result = dimension + "=" + valueIndex.toString()
      or
      prefix != "" and result = prefix + "," + dimension + "=" + valueIndex.toString()
    )
  )
}

private string getABaseMatrixAssignment(StrategyImpl strategy) {
  getBoundedBaseMatrixCombinationCount(strategy) > 0 and
  result =
    getBaseMatrixAssignmentPrefix(strategy, count(strategy.getAMatrixDimensionName()))
}

bindingset[assignment, name]
pragma[inline_late]
private int getBaseMatrixDimensionIndex(string assignment, string name) {
  exists(string component |
    component = assignment.splitAt(",") and
    component.splitAt("=", 0) = name and
    result = component.splitAt("=", 1).toInt()
  )
}

bindingset[strategy, assignment, name]
pragma[inline_late]
private string getBaseMatrixDimensionValue(
  StrategyImpl strategy, string assignment, string name
) {
  name = strategy.getAMatrixDimensionName() and
  result = strategy.getMatrixDimensionValue(name, getBaseMatrixDimensionIndex(assignment, name))
}

bindingset[strategy, assignment, name]
pragma[inline_late]
private YamlValue getBaseMatrixDimensionElement(
  StrategyImpl strategy, string assignment, string name
) {
  name = strategy.getAMatrixDimensionName() and
  result =
    strategy
        .getMatrix()
        .lookup(name)
        .(YamlSequence)
        .getElement(getBaseMatrixDimensionIndex(assignment, name))
}

bindingset[strategy, assignment, accessPath]
pragma[inline_late]
private YamlScalar getBaseMatrixAccessScalar(
  StrategyImpl strategy, string assignment, string accessPath
) {
  exists(string dimension, YamlValue element |
    dimension = strategy.getAMatrixDimensionName() and
    element = getBaseMatrixDimensionElement(strategy, assignment, dimension) and
    (
      accessPath.toLowerCase() = dimension.toLowerCase() and result = element
      or
      exists(string suffix |
        accessPath.toLowerCase().indexOf((dimension + ".").toLowerCase()) = 0 and
        suffix = accessPath.suffix(dimension.length() + 1) and
        result = resolveMatrixScalarAccess(element.(YamlMappingLikeNode), suffix)
      )
    )
  )
}

bindingset[root, accessPath]
pragma[inline_late]
private YamlScalar resolveMatrixScalarAccess(
  YamlMappingLikeNode root, string accessPath
) {
  not exists(accessPath.indexOf(".")) and result = root.getNode(accessPath)
  or
  exists(string first, string second |
    first = accessPath.splitAt(".", 0) and
    second = accessPath.splitAt(".", 1) and
    not exists(accessPath.splitAt(".", 2)) and
    result = root.getNode(first).(YamlMappingLikeNode).getNode(second)
  )
  or
  exists(string first, string second, string third |
    first = accessPath.splitAt(".", 0) and
    second = accessPath.splitAt(".", 1) and
    third = accessPath.splitAt(".", 2) and
    not exists(accessPath.splitAt(".", 3)) and
    result =
      root
          .getNode(first)
          .(YamlMappingLikeNode)
          .getNode(second)
          .(YamlMappingLikeNode)
          .getNode(third)
  )
  or
  exists(string first, string second, string third, string fourth |
    first = accessPath.splitAt(".", 0) and
    second = accessPath.splitAt(".", 1) and
    third = accessPath.splitAt(".", 2) and
    fourth = accessPath.splitAt(".", 3) and
    not exists(accessPath.splitAt(".", 4)) and
    result =
      root
          .getNode(first)
          .(YamlMappingLikeNode)
          .getNode(second)
          .(YamlMappingLikeNode)
          .getNode(third)
          .(YamlMappingLikeNode)
          .getNode(fourth)
  )
}

bindingset[strategy, kind]
pragma[inline_late]
private YamlMapping getMatrixControlEntry(StrategyImpl strategy, string kind, int index) {
  kind = ["include", "exclude"] and
  result = strategy.getMatrix().lookup(kind).(YamlSequence).getElement(index)
}

bindingset[entry]
pragma[inline_late]
private string getMatrixEntryKey(YamlMapping entry) {
  exists(YamlScalar key | entry.maps(key, _) and result = key.getValue())
}

bindingset[entry, key]
pragma[inline_late]
private string getMatrixEntryValue(YamlMapping entry, string key) {
  result = entry.lookup(key).(YamlScalar).getValue()
}

bindingset[strategy, assignment, entry]
pragma[inline_late]
private predicate matrixAssignmentMatchesExclude(
  StrategyImpl strategy, string assignment, YamlMapping entry
) {
  forall(string key | key = getMatrixEntryKey(entry) |
    key = strategy.getAMatrixDimensionName() and
    getBaseMatrixDimensionValue(strategy, assignment, key) = getMatrixEntryValue(entry, key)
  )
}

private string getAFilteredBaseMatrixAssignment(StrategyImpl strategy) {
  result = getABaseMatrixAssignment(strategy) and
  not exists(int index, YamlMapping entry |
    entry = getMatrixControlEntry(strategy, "exclude", index) and
    matrixAssignmentMatchesExclude(strategy, result, entry)
  )
}

bindingset[strategy, assignment, entry]
pragma[inline_late]
private predicate matrixIncludeMatchesBase(
  StrategyImpl strategy, string assignment, YamlMapping entry
) {
  forall(string key |
    key = getMatrixEntryKey(entry) and key = strategy.getAMatrixDimensionName()
  |
    getBaseMatrixDimensionValue(strategy, assignment, key) = getMatrixEntryValue(entry, key)
  )
}

private predicate isStandaloneMatrixInclude(StrategyImpl strategy, int includeIndex) {
  exists(getMatrixControlEntry(strategy, "include", includeIndex)) and
  not exists(string assignment, YamlMapping entry |
    assignment = getAFilteredBaseMatrixAssignment(strategy) and
    entry = getMatrixControlEntry(strategy, "include", includeIndex) and
    matrixIncludeMatchesBase(strategy, assignment, entry)
  )
}

private string getACandidateMatrixCombinationId(StrategyImpl strategy) {
  result = "base:" + getAFilteredBaseMatrixAssignment(strategy)
  or
  exists(int includeIndex |
    isStandaloneMatrixInclude(strategy, includeIndex) and
    result = "include:" + includeIndex.toString()
  )
}

bindingset[strategy]
pragma[inline_late]
private predicate hasBoundedMatrixCombinations(StrategyImpl strategy) {
  hasStaticMatrixDefinition(strategy) and
  exists(getBoundedBaseMatrixCombinationCount(strategy)) and
  count(getACandidateMatrixCombinationId(strategy)) <= maxExactMatrixCombinationCount()
}

private newtype TMatrixCombination =
  TBaseMatrixCombination(StrategyImpl strategy, string assignment) {
    hasBoundedMatrixCombinations(strategy) and
    assignment = getAFilteredBaseMatrixAssignment(strategy)
  } or
  TIncludedMatrixCombination(StrategyImpl strategy, int includeIndex) {
    hasBoundedMatrixCombinations(strategy) and
    isStandaloneMatrixInclude(strategy, includeIndex)
  }

/** One statically known effective combination of a matrix strategy. */
class MatrixCombinationImpl extends TMatrixCombination {
  StrategyImpl getStrategy() {
    this = TBaseMatrixCombination(result, _) or
    this = TIncludedMatrixCombination(result, _)
  }

  string getAssignment() {
    this = TBaseMatrixCombination(_, result)
    or
    exists(int index |
      this = TIncludedMatrixCombination(_, index) and result = "include=" + index.toString()
    )
  }

  string getAKey() {
    exists(string assignment |
      this = TBaseMatrixCombination(_, assignment) and
      (
        result = this.getStrategy().getAMatrixDimensionName()
        or
        exists(int includeIndex, YamlMapping entry |
          entry = getMatrixControlEntry(this.getStrategy(), "include", includeIndex) and
          matrixIncludeMatchesBase(this.getStrategy(), assignment, entry) and
          result = getMatrixEntryKey(entry)
        )
      )
    )
    or
    exists(int includeIndex, YamlMapping entry |
      this = TIncludedMatrixCombination(_, includeIndex) and
      entry = getMatrixControlEntry(this.getStrategy(), "include", includeIndex) and
      result = getMatrixEntryKey(entry)
    )
  }

  bindingset[accessPath]
  pragma[inline_late]
  private YamlScalar getAccessScalar(string accessPath) {
    exists(string assignment, int includeIndex, YamlMapping entry |
      this = TBaseMatrixCombination(_, assignment) and
      entry = getMatrixControlEntry(this.getStrategy(), "include", includeIndex) and
      matrixIncludeMatchesBase(this.getStrategy(), assignment, entry) and
      accessPath = getMatrixEntryKey(entry) and
      not exists(int laterIndex, YamlMapping laterEntry |
        laterIndex > includeIndex and
        laterEntry = getMatrixControlEntry(this.getStrategy(), "include", laterIndex) and
        matrixIncludeMatchesBase(this.getStrategy(), assignment, laterEntry) and
        accessPath = getMatrixEntryKey(laterEntry)
      ) and
      result = entry.lookup(accessPath)
    )
    or
    exists(string assignment |
      this = TBaseMatrixCombination(_, assignment) and
      not exists(int includeIndex, YamlMapping entry, string key |
        (key = accessPath.prefix(accessPath.indexOf(".")) or key = accessPath) and
        entry = getMatrixControlEntry(this.getStrategy(), "include", includeIndex) and
        matrixIncludeMatchesBase(this.getStrategy(), assignment, entry) and
        key = getMatrixEntryKey(entry)
      ) and
      result = getBaseMatrixAccessScalar(this.getStrategy(), assignment, accessPath)
    )
    or
    exists(int includeIndex, YamlMapping entry |
      this = TIncludedMatrixCombination(_, includeIndex) and
      entry = getMatrixControlEntry(this.getStrategy(), "include", includeIndex) and
      accessPath = getMatrixEntryKey(entry) and
      result = entry.lookup(accessPath)
    )
  }

  bindingset[accessPath]
  pragma[inline_late]
  string getValue(string accessPath) { result = this.getAccessScalar(accessPath).getValue() }

  bindingset[accessPath]
  pragma[inline_late]
  string getValueKind(string accessPath) {
    this.getAccessScalar(accessPath) instanceof YamlBool and result = "BooleanLiteral"
    or
    (
      this.getAccessScalar(accessPath) instanceof YamlInteger
      or
      this.getAccessScalar(accessPath) instanceof YamlFloat
    ) and
    result = "NumberLiteral"
    or
    this.getAccessScalar(accessPath) instanceof YamlNull and result = "NullLiteral"
    or
    this.getAccessScalar(accessPath) instanceof YamlString and result = "StringLiteral"
  }

  string toString() { result = this.getAssignment() }
}

class NeedsImpl extends AstNodeImpl, TNeedsNode {
  YamlMappingLikeNode n;

  NeedsImpl() { this = TNeedsNode(n) }

  override string toString() { result = n.toString() }

  override AstNodeImpl getAChildNode() { result.getNode() = getAnExpandedYamlChild*(n) }

  override JobImpl getParentNode() { result.getNode().lookup("needs") = n }

  override string getAPrimaryQlClass() { result = "NeedsImpl" }

  override Location getLocation() { result = n.getLocation() }

  override YamlMappingLikeNode getNode() { result = n }

  /** Gets a job that needs to be run before the job defining these needs. */
  JobImpl getANeededJob() {
    result.getId() = n.getNode(_).(YamlString).getValue() and
    result.getLocation().getFile() = n.getLocation().getFile()
  }
}

class OnImpl extends AstNodeImpl, TOnNode {
  YamlMappingLikeNode n;

  OnImpl() { this = TOnNode(n) }

  override string toString() { result = n.toString() }

  override AstNodeImpl getAChildNode() { result.getNode() = getAnExpandedYamlChild*(n) }

  override WorkflowImpl getParentNode() { result.getAChildNode() = this }

  override string getAPrimaryQlClass() { result = "OnImpl" }

  override Location getLocation() { result = n.getLocation() }

  override YamlMappingLikeNode getNode() { result = n }

  /** Gets an event that triggers the workflow. */
  EventImpl getAnEvent() { result.getParentNode() = this }
}

class EventImpl extends AstNodeImpl, TEventNode {
  YamlScalar e;
  YamlMappingLikeNode n;

  EventImpl() { this = TEventNode(e, n) }

  override string toString() { result = e.getValue() }

  override AstNodeImpl getAChildNode() { result.getNode() = getAnExpandedYamlChild*(n) }

  override OnImpl getParentNode() { result.getAChildNode() = this }

  override string getAPrimaryQlClass() { result = "EventImpl" }

  override Location getLocation() { result = e.getLocation() }

  override YamlScalar getNode() { result = e }

  /** Gets the name of the event that triggers the workflow. */
  string getName() { result = e.getValue() }

  /** Gets the Yaml Node associated with the event if any */
  YamlMappingLikeNode getValueNode() { result = n }

  /** Gets an activity type */
  string getAnActivityType() {
    result =
      n.(YamlMapping).lookup("types").(YamlMappingLikeNode).getNode(_).(YamlScalar).getValue()
  }

  /** Gets a string value for any property (eg: branches, branches-ignore, etc.) */
  string getAPropertyValue(string prop) {
    result = n.(YamlMapping).lookup(prop).(YamlMappingLikeNode).getNode(_).(YamlScalar).getValue()
  }

  /** Holds if the event has a property with the given name */
  predicate hasProperty(string prop) { exists(this.getAPropertyValue(prop)) }

  /** Holds if the event can be triggered by an external actor. */
  predicate isExternallyTriggerable() {
    // the job is triggered by an event that can be triggered externally
    // except for workflow_run which requires additional checks
    externallyTriggerableEventsDataModel(this.getName()) and
    not this.getName() = "workflow_run"
    or
    this.getName() = "workflow_run" and
    // workflow_run cannot be externally triggered if the triggering workflow runs in the context of the default branch
    // An attacker can change the triggering workflow from any event to `pull_request` to trigger the workflow
    // in that case, the triggering workflow will run in the context of the PR head branch
    not exists(this.getAPropertyValue("branches"))
    or
    // the event is `workflow_call` and there is a caller workflow that can be triggered externally
    this.getName() = "workflow_call" and
    (
      // there are hints that this workflow is meant to be called by external triggers
      exists(ExpressionImpl expr, string external_trigger |
        expr.getEnclosingWorkflow() = this.getEnclosingWorkflow() and
        expr.getExpression().matches("%github.event" + external_trigger + "%") and
        externallyTriggerableEventsDataModel(external_trigger)
      )
      or
      this.getEnclosingWorkflow()
          .(ReusableWorkflowImpl)
          .getACaller()
          .getATriggerEvent()
          .isExternallyTriggerable()
    )
  }

  predicate isPrivileged() {
    // the Job is triggered by an event other than `pull_request`, or `workflow_call`
    not this.getName() = "pull_request" and
    not this.getName() = "workflow_call"
    or
    // Reusable Workflow with a privileged caller or we cant find a caller
    this.getName() = "workflow_call" and
    (
      this.getEnclosingWorkflow().(ReusableWorkflowImpl).getACaller().isPrivileged() or
      not exists(this.getEnclosingWorkflow().(ReusableWorkflowImpl).getACaller())
    )
  }
}

class JobImpl extends AstNodeImpl, TJobNode {
  YamlMapping n;
  YamlNode jobOccurrence;
  string jobId;
  WorkflowImpl workflow;

  JobImpl() {
    this = TJobNode(n, jobOccurrence, jobId) and
    getAJobOccurrence(workflow.getNode(), n, jobOccurrence, jobId)
  }

  override string toString() { result = "Job: " + jobId }

  override AstNodeImpl getAChildNode() { result.getNode() = getAnExpandedYamlChild*(n) }

  override WorkflowImpl getParentNode() {
    getAJobOccurrence(result.getNode(), n, jobOccurrence, jobId)
  }

  override string getAPrimaryQlClass() { result = "JobImpl" }

  override Location getLocation() { result = n.getLocation() }

  override YamlMapping getNode() { result = n }

  /** Gets the ID of this job, as a string. */
  string getId() { result = jobId }

  YamlNode getOccurrence() { result = jobOccurrence }

  bindingset[this, value]
  pragma[inline_late]
  ScalarValueImpl getScalarValue(YamlScalar value) {
    hasAliasExpansion(jobOccurrence, n, value) and
    result = getScalarAtOccurrence(value, getAstOccurrence(jobOccurrence, jobOccurrence))
    or
    not hasAliasExpansion(jobOccurrence, n, value) and
    result = getScalarAtOccurrence(value, getAstOccurrence(value, value))
  }

  /** Gets the workflow this job belongs to. */
  WorkflowImpl getWorkflow() { result = workflow }

  override WorkflowImpl getEnclosingWorkflow() { result = workflow }

  EnvImpl getEnv() { result.getNode() = n.lookup("env") }

  /** Gets a needed job. */
  JobImpl getANeededJob() {
    exists(NeedsImpl needs |
      needs.getParentNode() = this and
      result = needs.getANeededJob()
    )
  }

  /** Gets the declaration of the outputs for the job. */
  OutputsImpl getOutputs() { result.getNode() = n.lookup("outputs") }

  /** Gets a Job output expression. */
  ExpressionImpl getAnOutputExpr() { result = this.getOutputs().getAnOutputExpr() }

  /** Gets a Job output expression given its name. */
  ExpressionImpl getOutputExpr(string name) { result = this.getOutputs().getOutputExpr(name) }

  /** Gets the condition that must be satisfied for this job to run. */
  IfImpl getIf() { result.getNode() = n.lookup("if") }

  string getContinueOnErrorValue() {
    result = n.lookup("continue-on-error").(YamlScalar).getValue()
  }

  ExpressionImpl getContinueOnErrorExpr() {
    result.getParentNode().getNode() = n.lookup("continue-on-error")
  }

  /** Gets the deployment environment to run the job on. */
  EnvironmentImpl getEnvironment() { result.getNode() = n.lookup("environment") }

  /** Gets the permissions for this job. */
  PermissionsImpl getPermissions() { result.getNode() = n.lookup("permissions") }

  predicate hasRequestedPermissions() {
    exists(this.getPermissions()) or
    not exists(this.getPermissions()) and exists(this.getEnclosingWorkflow().getPermissions())
  }

  bindingset[scope]
  pragma[inline_late]
  string getRequestedPermission(string scope) {
    exists(this.getPermissions()) and result = this.getPermissions().getConfiguredPermission(scope)
    or
    not exists(this.getPermissions()) and
    result = this.getEnclosingWorkflow().getPermissions().getConfiguredPermission(scope)
  }

  predicate mayRunWithoutReusableCaller() {
    not this.getEnclosingWorkflow() instanceof ReusableWorkflowImpl
    or
    not exists(this.getEnclosingWorkflow().(ReusableWorkflowImpl).getACaller())
    or
    exists(EventImpl event |
      this.getEnclosingWorkflow().getOn().getAnEvent() = event and
      not event.getName() = "workflow_call"
    )
  }

  bindingset[scope]
  pragma[inline_late]
  string getEffectivePermission(string scope) {
    effectivePermission(this, scope, result)
  }

  /** Gets the strategy for this job. */
  StrategyImpl getStrategy() { result.getNode() = n.lookup("strategy") }

  /** Gets the trigger event that starts this workflow. */
  override EventImpl getATriggerEvent() {
    if this.getEnclosingWorkflow() instanceof ReusableWorkflowImpl
    then
      result = this.getEnclosingWorkflow().(ReusableWorkflowImpl).getACaller().getATriggerEvent()
      or
      result = this.getEnclosingWorkflow().getATriggerEvent() and
      not result.getName() = "workflow_call"
    else result = this.getEnclosingWorkflow().getATriggerEvent()
  }

  /** Gets the runs-on field of the job. */
  string getARunsOnLabel() {
    exists(ScalarValueImpl lbl, YamlScalar label, YamlMappingLikeNode runson |
      runson = n.lookup("runs-on").(YamlMappingLikeNode)
    |
      (
        label = runson.getNode(_) and
        not label = runson.getNode("group")
        or
        label = runson.getNode("labels").(YamlMappingLikeNode).getNode(_)
      ) and lbl = this.getScalarValue(label) and
      (
        not exists(MatrixExpressionImpl e | e.getParentNode() = lbl) and
        result =
          lbl.getValue()
              .trim()
              .regexpReplaceAll("^('|\")", "")
              .regexpReplaceAll("('|\")$", "")
              .trim()
        or
        exists(MatrixExpressionImpl e |
          e.getParentNode() = lbl and
          result = e.getLiteralValues()
        )
      )
    )
  }

  private YamlValue getJobContainerDefinition() {
    result = getEvaluatedAnchorValue(n.lookup("container"))
  }

  private YamlValue getAServiceContainerDefinition() {
    result =
      getEvaluatedAnchorValue(
          getEvaluatedAnchorValue(n.lookup("services")).(YamlMapping).lookup(_)
        )
  }

  bindingset[this, container]
  pragma[inline_late]
  private ExpressionImpl getContainerImageExpr(YamlValue container) {
    exists(YamlScalar value |
      value = container.(YamlScalar)
      or
      value = getEvaluatedAnchorValue(container.(YamlMapping).lookup("image")).(YamlScalar)
    |
      hasAliasExpansion(jobOccurrence, n, value) and
      result =
        getExpressionAtOccurrence(value, getAstOccurrence(jobOccurrence, jobOccurrence))
      or
      not hasAliasExpansion(jobOccurrence, n, value) and
      result = getExpressionAtOccurrence(value, getAstOccurrence(value, value))
    )
  }

  ExpressionImpl getJobContainerImageExpr() {
    result = this.getContainerImageExpr(this.getJobContainerDefinition())
  }

  ExpressionImpl getAServiceContainerImageExpr() {
    result = this.getContainerImageExpr(this.getAServiceContainerDefinition())
  }

  private YamlValue getContainerDefinitionForImage(ExpressionImpl image) {
    image = this.getContainerImageExpr(result) and
    result = [this.getJobContainerDefinition(), this.getAServiceContainerDefinition()]
  }

  ScalarValueImpl getRegistryUsernameForContainerImage(ExpressionImpl image) {
    result =
      this.getScalarValue(
        getEvaluatedAnchorValue(
          this
              .getContainerDefinitionForImage(image)
              .(YamlMapping)
              .lookup("credentials")
              .(YamlMapping)
              .lookup("username")
                ).(YamlScalar)
              )
  }

  ExpressionImpl getRegistryPasswordExprForContainerImage(ExpressionImpl image) {
    exists(ScalarValueImpl password |
      password =
        this.getScalarValue(
          getEvaluatedAnchorValue(
            this
                .getContainerDefinitionForImage(image)
                .(YamlMapping)
                .lookup("credentials")
                .(YamlMapping)
                .lookup("password")
                ).(YamlScalar)
                  ) and
      result.getParentNode() = password
    )
  }

  private predicate hasExplicitSecretAccess() {
    this.(ExternalJobImpl).inheritsSecrets()
    or
    // the job accesses a secret other than GITHUB_TOKEN
    exists(SecretsExpressionImpl expr |
      (expr.getEnclosingJob() = this or not exists(expr.getEnclosingJob())) and
      expr.getEnclosingWorkflow() = this.getEnclosingWorkflow() and
      not expr.getFieldName() = "GITHUB_TOKEN"
    )
  }

  predicate hasKnownEffectivePermissions() {
    exists(string scope | scope = permissionScope() and exists(this.getEffectivePermission(scope)))
  }

  private predicate hasKnownEffectivePermissionsForEvent(EventImpl event) {
    exists(string scope, string permission |
      scope = permissionScope() and
      effectivePermissionForEvent(this, event, scope, permission)
    )
  }

  private predicate hasEffectiveWritePermission() {
    exists(string scope | scope = permissionScope() and this.getEffectivePermission(scope) = "write")
  }

  private predicate hasEffectiveWritePermissionForEvent(EventImpl event) {
    exists(string scope |
      scope = permissionScope() and
      effectivePermissionForEvent(this, event, scope, "write")
    )
  }

  private predicate hasRuntimeDataForEvent(EventImpl event) {
    exists(string path, string trigger, string name, string secrets_source, string perms |
      workflowDataModel(path, trigger, name, secrets_source, perms, _) and
      path.trim() = this.getLocation().getFile().getRelativePath() and
      name.trim().matches(this.getId() + "%") and
      trigger.trim() = event.getName()
    )
  }

  private predicate hasRuntimeWritePermissions() {
    // the effective runtime permissions have write access
    exists(string path, string trigger, string name, string secrets_source, string perms |
      workflowDataModel(path, trigger, name, secrets_source, perms, _) and
      path.trim() = this.getLocation().getFile().getRelativePath() and
      name.trim().matches(this.getId() + "%") and
      // We cannot trust the permissions for pull_request events since they depend on the
      // provenance of the head branch (local vs fork)
      not trigger.trim() = "pull_request" and
      perms.toLowerCase().matches("%write%")
    )
  }

  private predicate hasRuntimeWritePermissionsForEvent(EventImpl event) {
    exists(string path, string trigger, string name, string secrets_source, string perms |
      workflowDataModel(path, trigger, name, secrets_source, perms, _) and
      path.trim() = this.getLocation().getFile().getRelativePath() and
      name.trim().matches(this.getId() + "%") and
      trigger.trim() = event.getName() and
      not trigger.trim() = "pull_request" and
      perms.toLowerCase().matches("%write%")
    )
  }

  /** Holds if the job is privileged. */
  predicate isPrivileged() {
    // the job has privileged runtime permissions
    this.hasRuntimeWritePermissions()
    or
    // the job has an explicit secret accesses
    this.hasExplicitSecretAccess()
    or
    // the job has effective write permissions
    this.hasEffectiveWritePermission()
  }

  /** Holds if the action is privileged and externally triggerable. */
  predicate isPrivilegedExternallyTriggerable(EventImpl event) {
    this.getATriggerEvent() = event and
    // the job is triggerable by an external user
    event.isExternallyTriggerable() and
    // no matter if `pull_request` is granted write permissions or access to secrets
    // when the job is triggered by a `pull_request` event from a fork, they will get revoked
    not event.getName() = "pull_request" and
    (
      // the job accesses secrets
      this.hasExplicitSecretAccess()
      or
      // runtime data grants write access for this event
      this.hasRuntimeWritePermissionsForEvent(event)
      or
      // static permissions grant write access for this event
      this.hasEffectiveWritePermissionForEvent(event)
      or
      // the trigger event is __normally__ privileged
      event.isPrivileged() and
      // and we have no runtime data to prove otherwise
      not this.hasRuntimeDataForEvent(event) and
      // and static permissions do not prove that the job is non-privileged
      not this.hasKnownEffectivePermissionsForEvent(event)
    )
  }
}

private predicate effectivePermission(JobImpl job, string scope, string permission) {
  scope = permissionScope() and
  (
    job.hasRequestedPermissions() and
    maximumEffectivePermission(job, scope, permission)
    or
    not job.hasRequestedPermissions() and
    exists(ExternalJobImpl caller |
      job.getEnclosingWorkflow().(ReusableWorkflowImpl).getACaller() = caller and
      maximumEffectivePermission(caller, scope, permission)
    )
  )
}

private predicate maximumEffectivePermission(JobImpl job, string scope, string permission) {
  scope = permissionScope() and
  (
    job.mayRunWithoutReusableCaller() and
    (
      job.hasRequestedPermissions() and permission = job.getRequestedPermission(scope)
      or
      not job.hasRequestedPermissions() and permission = maximumPermission(scope)
    )
    or
    exists(ExternalJobImpl caller, string cap |
      job.getEnclosingWorkflow().(ReusableWorkflowImpl).getACaller() = caller and
      maximumEffectivePermission(caller, scope, cap) and
      (
        exists(string requested |
          job.hasRequestedPermissions() and
          requested = job.getRequestedPermission(scope) and
          permission = restrictPermission(requested, cap)
        )
        or
        not job.hasRequestedPermissions() and permission = cap
      )
    )
  )
}

private predicate effectivePermissionForEvent(
  JobImpl job, EventImpl event, string scope, string permission
) {
  scope = permissionScope() and
  (
    job.hasRequestedPermissions() and
    maximumEffectivePermissionForEvent(job, event, scope, permission)
    or
    not job.hasRequestedPermissions() and
    exists(ExternalJobImpl caller |
      job.getEnclosingWorkflow().(ReusableWorkflowImpl).getACaller() = caller and
      maximumEffectivePermissionForEvent(caller, event, scope, permission)
    )
  )
}

private predicate maximumEffectivePermissionForEvent(
  JobImpl job, EventImpl event, string scope, string permission
) {
  scope = permissionScope() and
  (
    job.getEnclosingWorkflow().getOn().getAnEvent() = event and
    not event.getName() = "workflow_call" and
    (
      job.hasRequestedPermissions() and permission = job.getRequestedPermission(scope)
      or
      not job.hasRequestedPermissions() and permission = maximumPermission(scope)
    )
    or
    exists(ExternalJobImpl caller, string cap |
      job.getEnclosingWorkflow().(ReusableWorkflowImpl).getACaller() = caller and
      maximumEffectivePermissionForEvent(caller, event, scope, cap) and
      (
        exists(string requested |
          job.hasRequestedPermissions() and
          requested = job.getRequestedPermission(scope) and
          permission = restrictPermission(requested, cap)
        )
        or
        not job.hasRequestedPermissions() and permission = cap
      )
    )
  )
}

abstract class StepsContainerImpl extends AstNodeImpl {
  /** Gets any steps that are defined within this job. */
  abstract StepImpl getAStep();

  /** Gets any directly or transitively contained step. */
  StepImpl getAContainedStep() {
    result = this.getAStep()
    or
    result = this.getAStep().(ParallelStepImpl).getAContainedStep()
  }

  /** Gets the step at the given index within this job. */
  abstract StepImpl getStep(int i);
}

class RunsImpl extends StepsContainerImpl, TRunsNode {
  YamlMapping n;

  RunsImpl() { this = TRunsNode(n) }

  override string toString() { result = n.toString() }

  override AstNodeImpl getAChildNode() { result.getNode() = getAnExpandedYamlChild*(n) }

  override CompositeActionImpl getParentNode() { result.getAChildNode() = this }

  override string getAPrimaryQlClass() { result = "RunsImpl" }

  override Location getLocation() { result = n.getLocation() }

  override YamlMapping getNode() { result = n }

  /** Gets the action that this `runs` mapping is in. */
  CompositeActionImpl getAction() { result = this.getParentNode() }

  /** Gets any steps that are defined within this job. */
  override StepImpl getAStep() {
    exists(YamlSequence steps, YamlNode occurrence, int index |
      steps = getEvaluatedAnchorValue(getRawMappingValue(n, "steps")) and
      occurrence = steps.getElementNode(index) and
      result.getNode() = getEvaluatedAnchorValue(occurrence) and
      result.getContainerOccurrence() = n and
      result.getElementOccurrence() = occurrence
    )
  }

  /** Gets the step at the given index within this job. */
  override StepImpl getStep(int i) {
    exists(YamlSequence steps, YamlNode occurrence |
      steps = getEvaluatedAnchorValue(getRawMappingValue(n, "steps")) and
      occurrence = steps.getElementNode(i) and
      result.getNode() = getEvaluatedAnchorValue(occurrence) and
      result.getContainerOccurrence() = n and
      result.getElementOccurrence() = occurrence
    )
  }
}

class LocalJobImpl extends JobImpl, StepsContainerImpl {
  LocalJobImpl() { n.maps(any(YamlString s | s.getValue() = "steps"), _) }

  /** Gets any steps that are defined within this job. */
  override StepImpl getAStep() {
    exists(YamlSequence steps, YamlNode occurrence, int index |
      steps = getEvaluatedAnchorValue(getRawMappingValue(n, "steps")) and
      occurrence = steps.getElementNode(index) and
      result.getNode() = getEvaluatedAnchorValue(occurrence) and
      result.getContainerOccurrence() = this.getOccurrence() and
      result.getElementOccurrence() = occurrence
    )
  }

  /** Gets the step at the given index within this job. */
  override StepImpl getStep(int i) {
    exists(YamlSequence steps, YamlNode occurrence |
      steps = getEvaluatedAnchorValue(getRawMappingValue(n, "steps")) and
      occurrence = steps.getElementNode(i) and
      result.getNode() = getEvaluatedAnchorValue(occurrence) and
      result.getContainerOccurrence() = this.getOccurrence() and
      result.getElementOccurrence() = occurrence
    )
  }
}

class StepImpl extends AstNodeImpl, TStepNode {
  YamlMapping n;
  AstOccurrence occurrence;

  StepImpl() { this = TStepNode(n, occurrence) }

  override string toString() { result = n.toString() }

  override AstNodeImpl getAChildNode() { result.getNode() = getAnExpandedYamlChild*(n) }

  override AstNodeImpl getParentNode() {
    exists(LocalJobImpl job |
      job.getOccurrence() = occurrence.getContainer() and result = job
    )
    or
    exists(RunsImpl runs |
      runs.getNode() = occurrence.getContainer() and result = runs
    )
    or
    exists(ParallelStepImpl parallel |
      parallel.getElementOccurrence() = occurrence.getContainer() and result = parallel
    )
  }

  override string getAPrimaryQlClass() { result = "StepImpl" }

  override Location getLocation() { result = n.getLocation() }

  override YamlMapping getNode() { result = n }

  AstOccurrence getOccurrence() { result = occurrence }

  YamlNode getContainerOccurrence() { result = occurrence.getContainer() }

  YamlNode getElementOccurrence() { result = occurrence.getElement() }

  bindingset[this, value]
  pragma[inline_late]
  ScalarValueImpl getScalarValue(YamlScalar value) {
    hasStepAliasContext(n, occurrence.getContainer(), occurrence.getElement(), value) and
    result = getScalarAtOccurrence(value, occurrence)
    or
    not hasStepAliasContext(n, occurrence.getContainer(), occurrence.getElement(), value) and
    result = getScalarAtOccurrence(value, getAstOccurrence(value, value))
  }

  override JobImpl getEnclosingJob() {
    result = getJobAtOccurrence(occurrence.getContainer())
    or
    exists(RunsImpl runs |
      runs.getNode() = occurrence.getContainer() and result = runs.getAction().getACallerJob()
    )
    or
    exists(ParallelStepImpl parallel |
      parallel.getElementOccurrence() = occurrence.getContainer() and
      result = parallel.getEnclosingJob()
    )
  }

  override WorkflowImpl getEnclosingWorkflow() { result = this.getEnclosingJob().getWorkflow() }

  override EventImpl getATriggerEvent() { result = this.getEnclosingJob().getATriggerEvent() }

  EnvImpl getEnv() { result.getNode() = n.lookup("env") }

  /** Gets the ID of this step, if any. */
  string getId() { result = n.lookup("id").(YamlString).getValue() }

  /** Gets the value of the `if` field in this step, if any. */
  IfImpl getIf() { result.getNode() = n.lookup("if") }

  string getContinueOnErrorValue() {
    result = n.lookup("continue-on-error").(YamlScalar).getValue()
  }

  ExpressionImpl getContinueOnErrorExpr() {
    result.getParentNode().getNode() = n.lookup("continue-on-error")
  }

  /** Gets the Runs or LocalJob that this step is in. */
  StepsContainerImpl getContainer() {
    result = this.getParentNode().(RunsImpl) or
    result = this.getParentNode().(LocalJobImpl) or
    result = this.getParentNode().(ParallelStepImpl)
  }

  predicate runsInBackground() { n.lookup("background").(YamlScalar).getValue() = "true" }

  predicate mayRunInForeground() {
    not exists(n.lookup("background"))
    or
    not n.lookup("background").(YamlScalar).getValue() = "true"
  }

  StepImpl getNextStep() {
    // if step is a uses step calling a local composite action, we should follow the called step
    this instanceof UsesStepImpl and
    exists(CompositeActionImpl a |
      a.getACallerStep() = this and
      result = a.getRuns().getStep(0)
    )
    or
    // if step is the last step in a composite action, we should follow the next step in the caller
    exists(RunsImpl runs, StepsContainerImpl caller_container, StepImpl caller, int i |
      this.getContainer() = runs and
      runs.getStep(count(StepImpl s | runs.getAStep() = s | s) - 1) = this and
      runs.getEnclosingCompositeAction().getACallerStep() = caller and
      caller.getContainer() = caller_container and
      caller_container.getStep(i) = caller and
      caller_container.getStep(i + 1) = result
    )
    or
    // parallel children join at the containing parallel step
    this.getContainer() instanceof ParallelStepImpl and result = this.getContainer()
    or
    // next step in the same job/runs
    exists(int i |
      not this.getContainer() instanceof ParallelStepImpl and
      this.getContainer().getStep(i) = this and
      result = this.getContainer().getStep(i + 1)
    )
  }

  /** Gets a step that follows this step. */
  StepImpl getAFollowingStep() {
    (
      // next steps in the same job/runs
      exists(int i, int j |
        not this.getContainer() instanceof ParallelStepImpl and
        not this instanceof BackgroundStepImpl and
        this.getContainer().getStep(i) = this and
        result = this.getContainer().getStep(j) and
        i < j
      )
      or
      // foreground steps launched before a background barrier do not follow completion
      this instanceof BackgroundStepImpl and
      (
        result = this.(BackgroundStepImpl).getBarrier()
        or
        result = this.(BackgroundStepImpl).getBarrier().getAFollowingStep()
      )
      or
      // parallel children all precede their join and the steps after it
      this.getContainer() instanceof ParallelStepImpl and
      (
        result = this.getContainer()
        or
        result = this.getContainer().(ParallelStepImpl).getAFollowingStep()
      )
      or
      // next steps of the caller (in a composite action step)
      result = this.getEnclosingCompositeAction().getACallerStep().getAFollowingStep()
      or
      // if any of the next steps is a call to a local composite actions, we should follow it
      exists(int i, int j, CompositeActionImpl a |
        this.getContainer().getStep(i) = this and
        this.getContainer().getStep(j) = a.getACallerStep() and
        i < j and
        result = a.getRuns().getAStep()
      )
      or
      // a following parallel group may execute any of its children
      exists(int i, int j, ParallelStepImpl parallel |
        this.getContainer().getStep(i) = this and
        this.getContainer().getStep(j) = parallel and
        i < j and
        result = parallel.getAStep()
      )
    )
  }
}

class BackgroundStepImpl extends StepImpl {
  BackgroundStepImpl() {
    this.runsInBackground() and (this instanceof RunImpl or this instanceof UsesStepImpl)
  }

  BackgroundCompletionImpl getCompletion() {
    result.getBackgroundStep() = this
  }

  StepImpl getBarrier() { isFirstBackgroundBarrier(this, result) }
}

class BackgroundCompletionImpl extends AstNodeImpl, TBackgroundCompletionNode {
  YamlMapping n;
  AstOccurrence occurrence;

  BackgroundCompletionImpl() { this = TBackgroundCompletionNode(n, occurrence) }

  override string toString() { result = "Complete " + this.getBackgroundStep().toString() }

  override AstNodeImpl getAChildNode() { none() }

  override BackgroundStepImpl getParentNode() { result = this.getBackgroundStep() }

  override string getAPrimaryQlClass() { result = "BackgroundCompletionImpl" }

  override Location getLocation() { result = n.getLocation() }

  override YamlMapping getNode() { result = n }

  BackgroundStepImpl getBackgroundStep() {
    result.getNode() = n and
    result.getOccurrence() = occurrence
  }
}

class WaitStepImpl extends StepImpl {
  WaitStepImpl() { exists(n.lookup("wait")) }

  string getATargetId() {
    result = n.lookup("wait").(YamlScalar).getValue()
    or
    result = n.lookup("wait").(YamlSequence).getElement(_).(YamlScalar).getValue()
  }

  BackgroundStepImpl getATargetStep() {
    result.getId() = this.getATargetId() and isFirstBackgroundBarrier(result, this)
  }

  override string toString() { result = "Wait Step: " + this.getATargetId() }
}

class WaitAllStepImpl extends StepImpl {
  WaitAllStepImpl() {
    n.lookup("wait-all") instanceof YamlNull
    or
    n.lookup("wait-all").(YamlScalar).getValue() = "true"
  }

  BackgroundStepImpl getATargetStep() {
    isFirstBackgroundBarrier(result, this)
  }

  override string toString() { result = "Wait All Step" }
}

class CancelStepImpl extends StepImpl {
  CancelStepImpl() { exists(n.lookup("cancel").(YamlScalar)) }

  string getTargetId() { result = n.lookup("cancel").(YamlScalar).getValue() }

  BackgroundStepImpl getTargetStep() {
    result.getId() = this.getTargetId() and isFirstBackgroundBarrier(result, this)
  }

  override string toString() { result = "Cancel Step: " + this.getTargetId() }
}

class ParallelStepImpl extends StepImpl, StepsContainerImpl {
  ParallelStepImpl() { exists(getRawMappingValue(n, "parallel")) }

  override StepImpl getAStep() {
    exists(YamlSequence steps, YamlNode childOccurrence, int index |
      steps = getEvaluatedAnchorValue(getRawMappingValue(n, "parallel")) and
      childOccurrence = steps.getElementNode(index) and
      result.getNode() = getEvaluatedAnchorValue(childOccurrence) and
      result.getContainerOccurrence() = this.getElementOccurrence() and
      result.getElementOccurrence() = childOccurrence
    )
  }

  override StepImpl getStep(int i) {
    exists(YamlSequence steps, YamlNode childOccurrence |
      steps = getEvaluatedAnchorValue(getRawMappingValue(n, "parallel")) and
      childOccurrence = steps.getElementNode(i) and
      result.getNode() = getEvaluatedAnchorValue(childOccurrence) and
      result.getContainerOccurrence() = this.getElementOccurrence() and
      result.getElementOccurrence() = childOccurrence
    )
  }

  override string toString() { result = "Parallel Step" }
}

private predicate isBackgroundBarrierFor(StepImpl barrier, BackgroundStepImpl background) {
  barrier.(WaitStepImpl).getATargetId() = background.getId()
  or
  barrier instanceof WaitAllStepImpl
  or
  barrier.(CancelStepImpl).getTargetId() = background.getId()
}

private predicate isFirstBackgroundBarrier(
  BackgroundStepImpl background, StepImpl barrier
) {
  exists(int backgroundIndex, int barrierIndex |
    background.getContainer() = barrier.getContainer() and
    barrier.getContainer().getStep(backgroundIndex) = background and
    barrier.getContainer().getStep(barrierIndex) = barrier and
    backgroundIndex < barrierIndex and
    isBackgroundBarrierFor(barrier, background) and
    not exists(int earlierIndex, StepImpl earlier |
      barrier.getContainer().getStep(earlierIndex) = earlier and
      backgroundIndex < earlierIndex and
      earlierIndex < barrierIndex and
      isBackgroundBarrierFor(earlier, background)
    )
  )
}

class EnvironmentImpl extends AstNodeImpl, TEnvironmentNode {
  YamlValue n;

  EnvironmentImpl() { this = TEnvironmentNode(n) }

  override string toString() { result = n.toString() }

  override AstNodeImpl getAChildNode() { result.getNode() = getAnExpandedYamlChild*(n) }

  override AstNodeImpl getParentNode() { result.getAChildNode() = this }

  override string getAPrimaryQlClass() { result = "EnvironmentImpl" }

  override Location getLocation() { result = n.getLocation() }

  override YamlValue getNode() { result = n }

  private YamlValue getPropertyNode(string name) {
    result = n.(YamlMapping).lookup(name)
    or
    name = "name" and result = n.(YamlScalar)
  }

  /** Gets the environment name. */
  string getName() { result = this.getPropertyNode("name").(YamlScalar).getValue() }

  /** Gets an expression in the environment name. */
  ExpressionImpl getNameExpr() { result.getParentNode().getNode() = this.getPropertyNode("name") }

  /** Gets the environment URL. */
  string getUrl() { result = this.getPropertyNode("url").(YamlScalar).getValue() }

  /** Gets an expression in the environment URL. */
  ExpressionImpl getUrlExpr() { result.getParentNode().getNode() = this.getPropertyNode("url") }

  /** Gets whether this environment creates a deployment. */
  string getDeploymentValue() {
    result = this.getPropertyNode("deployment").(YamlScalar).getValue()
  }

  /** Gets an expression controlling whether this environment creates a deployment. */
  ExpressionImpl getDeploymentExpr() {
    result.getParentNode().getNode() = this.getPropertyNode("deployment")
  }
}

class IfImpl extends AstNodeImpl, TIfNode {
  YamlValue n;

  IfImpl() { this = TIfNode(n) }

  override string toString() { result = n.toString() }

  override AstNodeImpl getAChildNode() { result.getNode() = getAnExpandedYamlChild*(n) }

  override AstNodeImpl getParentNode() { result.getAChildNode() = this }

  override string getAPrimaryQlClass() { result = "IfImpl" }

  override Location getLocation() { result = n.getLocation() }

  override YamlScalar getNode() { result = n }

  /** Gets the condition that must be satisfied for this job to run. */
  string getCondition() { result = n.(YamlScalar).getValue() }

  /** Gets the condition that must be satisfied for this job to run. */
  ExpressionImpl getConditionExpr() { result.getParentNode().getNode() = n }

  /** Get condition scalar style. */
  string getConditionStyle() { result = n.(YamlScalar).getStyle() }
}

class EnvImpl extends AstNodeImpl, TEnvNode {
  YamlMapping n;

  EnvImpl() { this = TEnvNode(n) }

  override string toString() { result = n.toString() }

  override AstNodeImpl getAChildNode() { result.getNode() = getAnExpandedYamlChild*(n) }

  override AstNodeImpl getParentNode() {
    result.(JobImpl).getEnv() = this or
    result.(StepImpl).getEnv() = this or
    result.(WorkflowImpl).getEnv() = this
  }

  override string getAPrimaryQlClass() { result = "EnvImpl" }

  override Location getLocation() { result = n.getLocation() }

  override YamlMapping getNode() { result = n }

  /** Gets an environment variable value given its name. */
  ScalarValueImpl getEnvVarValue(string name) { n.lookup(name) = result.getNode() }

  /** Gets an environment variable value. */
  ScalarValueImpl getAnEnvVarValue() { n.lookup(_) = result.getNode() }

  /** Gets an environment variable expressin given its name. */
  ExpressionImpl getEnvVarExpr(string name) { n.lookup(name) = result.getParentNode().getNode() }

  /** Gets an environment variable expression. */
  ExpressionImpl getAnEnvVarExpr() { n.lookup(_) = result.getParentNode().getNode() }
}

abstract class UsesImpl extends AstNodeImpl {
  abstract string getCallee();

  abstract string getCallableName();

  abstract ScalarValueImpl getCalleeNode();

  abstract predicate isRemoteCall();

  abstract string getVersion();

  bindingset[this, value]
  pragma[inline_late]
  private ScalarValueImpl getScalarValue(YamlScalar value) {
    exists(StepImpl step |
      this = step and
      result = step.getScalarValue(value)
    )
    or
    exists(JobImpl job |
      this = job and
      result = job.getScalarValue(value)
    )
  }

  int getMajorVersion() {
    result = this.getVersion().regexpReplaceAll("^v", "").regexpReplaceAll("\\..*", "").toInt()
  }

  /** Gets the argument expression for the given key. */
  string getArgument(string key) {
    exists(ScalarValueImpl scalar, YamlScalar value |
      value = this.getNode().(YamlMapping).lookup("with").(YamlMapping).lookup(key) and
      scalar = this.getScalarValue(value) and
      result = scalar.getValue()
    )
  }

  /** Gets the argument expression for the given key (if it exists). */
  ExpressionImpl getArgumentExpr(string key) {
    exists(ScalarValueImpl scalar, YamlScalar value |
      value = this.getNode().(YamlMapping).lookup("with").(YamlMapping).lookup(key) and
      scalar = this.getScalarValue(value) and
      result.getParentNode() = scalar
    )
  }
}

/** A Uses step represents a call to an action that is defined in a GitHub repository. */
class UsesStepImpl extends StepImpl, UsesImpl {
  YamlScalar u;

  UsesStepImpl() { this.getNode().lookup("uses") = u }

  override AstNodeImpl getAChildNode() { result.getNode() = getAnExpandedYamlChild*(n) }

  /** Gets the owner and name of the repository where the Action comes from, e.g. `actions/checkout` in `actions/checkout@v2`. */
  override string getCallee() {
    if u.getValue().indexOf("@") > 0
    then result = u.getValue().prefix(u.getValue().indexOf("@"))
    else result = u.getValue()
  }

  private predicate isLocalCall() { u.getValue().matches(["./%", ".github/%"]) }

  override predicate isRemoteCall() { not this.isLocalCall() }

  private predicate hasModeledExternalCallee() {
    exists(string owner, string repo, string action_path, string requested_ref,
      string resolved_commit_sha, string local_path |
      externalCompositeActionDataModel(owner, repo, action_path, requested_ref,
        resolved_commit_sha, local_path) and
      this.getCallee() = externalCompositeActionName(owner, repo, action_path) and
      this.getVersion() = requested_ref.trim()
    )
  }

  private predicate hasExternalEnclosingCompositeAction() {
    exists(CompositeActionImpl action |
      action = this.getEnclosingCompositeAction() and action.isExternalCompositeAction()
    )
  }

  private predicate hasModeledExternalEnclosingCompositeAction() {
    exists(CompositeActionImpl action, string owner, string repo, string action_path,
      string requested_ref, string resolved_commit_sha, string local_path |
      action = this.getEnclosingCompositeAction() and
      action.getAnExternalCompositeActionModel(owner, repo, action_path, requested_ref,
        resolved_commit_sha, local_path)
    )
  }

  override string getCallableName() {
    this.isLocalCall() and
    (
      this.hasModeledExternalEnclosingCompositeAction()
      or
      not this.hasExternalEnclosingCompositeAction()
    ) and
    result = this.getCallee()
    or
    not this.isLocalCall() and
    this.hasModeledExternalCallee() and
    result = this.getCallee() + "@" + this.getVersion()
  }

  override ScalarValueImpl getCalleeNode() { result = this.getScalarValue(u) }

  /** Gets the version reference used when checking out the Action, e.g. `v2` in `actions/checkout@v2`. */
  override string getVersion() { result = u.getValue().suffix(u.getValue().indexOf("@") + 1) }

  override string toString() {
    if exists(this.getId()) then result = "Uses Step: " + this.getId() else result = "Uses Step"
  }
}

/**
 * Gets a regular expression that parses an `owner/repo@version` reference within a `uses` field in an Actions job step.
 * local repo: octo-org/this-repo/.github/workflows/workflow-1.yml@172239021f7ba04fe7327647b213799853a9eb89
 * local repo: ./.github/workflows/workflow-2.yml
 * remote repo: octo-org/another-repo/.github/workflows/workflow.yml@v1
 */
private string repoUsesParser() { result = "([^/]+)/([^/]+)/([^@]+)@(.+)" }

private string pathUsesParser() { result = "\\./(.+)" }

class ExternalJobImpl extends JobImpl, UsesImpl {
  YamlScalar u;

  ExternalJobImpl() { n.lookup("uses") = u }

  string getSecret(string key) {
    exists(ScalarValueImpl scalar, YamlScalar value |
      value = n.lookup("secrets").(YamlMapping).lookup(key) and
      scalar = this.getScalarValue(value) and
      result = scalar.getValue()
    )
  }

  ExpressionImpl getASecretExpr() { result = this.getSecretExpr(_) }

  ExpressionImpl getSecretExpr(string key) {
    exists(ScalarValueImpl scalar, YamlScalar value |
      value = n.lookup("secrets").(YamlMapping).lookup(key) and
      scalar = this.getScalarValue(value) and
      result.getParentNode() = scalar
    )
  }

  predicate inheritsSecrets() { n.lookup("secrets").(YamlScalar).getValue() = "inherit" }

  override string getCallee() {
    if u.getValue().matches("./%")
    then result = u.getValue().regexpCapture(pathUsesParser(), 1)
    else
      result =
        u.getValue().regexpCapture(repoUsesParser(), 1) + "/" +
          u.getValue().regexpCapture(repoUsesParser(), 2) + "/" +
          u.getValue().regexpCapture(repoUsesParser(), 3)
  }

  private predicate isLocalCall() { u.getValue().matches("./%") }

  override predicate isRemoteCall() { not this.isLocalCall() }

  private predicate hasExternalEnclosingWorkflow() {
    exists(ReusableWorkflowImpl enclosing_workflow |
      enclosing_workflow = this.getEnclosingWorkflow() and
      enclosing_workflow.isExternalReusableWorkflow()
    )
  }

  private predicate hasModeledExternalCallee() {
    exists(string owner, string repo, string workflow_path, string requested_ref,
      string resolved_commit_sha, string local_path |
      externalReusableWorkflowDataModel(owner, repo, workflow_path, requested_ref,
        resolved_commit_sha, local_path) and
      this.getCallee() = owner.trim() + "/" + repo.trim() + "/" + workflow_path.trim() and
      this.getVersion() = requested_ref.trim()
    )
  }

  override string getCallableName() {
    this.isLocalCall() and
    exists(ReusableWorkflowImpl enclosing_workflow, string owner, string repo, string workflow_path,
      string requested_ref, string resolved_commit_sha, string local_path |
      enclosing_workflow = this.getEnclosingWorkflow() and
      enclosing_workflow.getAnExternalReusableWorkflowModel(owner, repo, workflow_path, requested_ref,
        resolved_commit_sha, local_path) and
      result =
        owner.trim() + "/" + repo.trim() + "/" + this.getCallee() + "@" + requested_ref.trim()
    )
    or
    this.isLocalCall() and
    not this.hasExternalEnclosingWorkflow() and
    result = this.getCallee()
    or
    not this.isLocalCall() and
    this.hasModeledExternalCallee() and
    result = this.getCallee() + "@" + this.getVersion()
  }

  override ScalarValueImpl getCalleeNode() { result = this.getScalarValue(u) }

  /** Gets the version reference used when checking out the Action, e.g. `v2` in `actions/checkout@v2`. */
  override string getVersion() {
    exists(YamlString name |
      n.lookup("uses") = name and
      not name.getValue().matches("\\.%") and
      result = name.getValue().regexpCapture(repoUsesParser(), 4)
    )
  }
}

class RunImpl extends StepImpl {
  YamlScalar script;
  ScalarValueImpl scriptScalar;

  RunImpl() {
    this.getNode().lookup("run") = script and
    scriptScalar = this.getScalarValue(script)
  }

  override string toString() {
    if exists(this.getId()) then result = "Run Step: " + this.getId() else result = "Run Step"
  }

  /** Gets the working directory for this `run` mapping. */
  string getWorkingDirectory() {
    if exists(n.lookup("working-directory").(YamlString).getValue())
    then
      result =
        n.lookup("working-directory")
            .(YamlString)
            .getValue()
            .regexpReplaceAll("^\\./", "GITHUB_WORKSPACE/")
    else result = "GITHUB_WORKSPACE/"
  }

  /** Gets the shell for this `run` mapping. */
  string getShell() {
    if exists(n.lookup("shell"))
    then result = n.lookup("shell").(YamlString).getValue()
    else
      if exists(this.getInScopeDefaultValue("run", "shell"))
      then result = this.getInScopeDefaultValue("run", "shell").getValue()
      else
        if this.getEnclosingJob().getARunsOnLabel().matches(["ubuntu%", "macos%"])
        then result = "bash"
        else
          if this.getEnclosingJob().getARunsOnLabel().matches("windows%")
          then result = "pwsh"
          else result = "bash"
  }

  ShellScriptImpl getScript() { result = scriptScalar }

  ExpressionImpl getAnScriptExpr() { result.getParentNode() = scriptScalar }
}

/**
 * Holds if `${{ e }}` is a GitHub Actions expression evaluated within this YAML string.
 * See https://docs.github.com/en/free-pro-team@latest/actions/reference/context-and-expression-syntax-for-github-actions.
 * Only finds simple expressions like `${{ github.event.comment.body }}`, where the expression contains only alphanumeric characters, underscores, dots, or dashes.
 * Does not identify more complicated expressions like `${{ fromJSON(env.time) }}`, or ${{ format('{{Hello {0}!}}', github.event.head_commit.author.name) }}
 */
bindingset[s]
string getASimpleReferenceExpression(string s, int offset) {
  // If the expression is ${{ inputs.foo == "foo" }} we should not consider it as a simple reference
  // check that expression matches a simple reference or several simple references ORed with ||
  s.regexpMatch("([A-Za-z0-9'\\\"_\\[\\]\\*\\(\\)\\.\\-]+)(\\s*\\|\\|\\s*[A-Za-z0-9'\\\"_\\[\\]\\*\\(\\)\\.\\-]+)*") and
  // We use `regexpFind` to obtain *all* matches of `${{...}}`,
  // not just the last (greedy match) or first (reluctant match).
  result =
    s.trim()
        .regexpFind("[A-Za-z0-9'\"_\\[\\]\\*\\(\\)\\.\\-]+", _, offset)
        .regexpCapture("([A-Za-z0-9'\"_\\[\\]\\*\\(\\)\\.\\-]+)", _)
}

bindingset[s]
string getAFromJsonReferenceExpression(string s, int offset) {
  // We use `regexpFind` to obtain *all* matches of `${{...}}`,
  // not just the last (greedy match) or first (reluctant match).
  result =
    s.trim()
        .regexpFind("(?i)fromjson\\([a-z0-9'\"_\\[\\]\\*\\(\\)\\.\\-]+\\)[a-z0-9'\"_\\[\\]\\*\\(\\)\\.\\-]*",
          _, offset)
        .regexpCapture("(?i)fromjson\\(([a-z0-9'\"_\\[\\]\\*\\(\\)\\.\\-]+)\\)[a-z0-9'\"_\\[\\]\\*\\(\\)\\.\\-]*",
          1)
}

bindingset[s]
string getAToJsonReferenceExpression(string s, int offset) {
  // We use `regexpFind` to obtain *all* matches of `${{...}}`,
  // not just the last (greedy match) or first (reluctant match).
  result =
    s.trim()
        .regexpFind("(?i)tojson\\(\\s*[a-z0-9'\"_\\[\\]\\*\\(\\)\\.\\-]+\\)[a-z0-9'\"_\\[\\]\\*\\(\\)\\.\\-]*",
          _, offset)
        .regexpCapture("(?i)tojson\\(\\s*([a-z0-9'\"_\\[\\]\\*\\(\\)\\.\\-]+)\\)[a-z0-9'\"_\\[\\]\\*\\(\\)\\.\\-]*",
          1)
}

bindingset[s]
string getAJsonReferenceExpression(string s, int offset) {
  // We use `regexpFind` to obtain *all* matches of `${{...}}`,
  // not just the last (greedy match) or first (reluctant match).
  result =
    s.trim()
        .regexpFind("(?i)(from|to)json\\([a-z0-9'\"_\\[\\]\\*\\(\\)\\.\\-]+\\)[a-z0-9'\"_\\[\\]\\*\\(\\)\\.\\-]*",
          _, offset)
        .regexpCapture("(?i)(from|to)json\\(([a-z0-9'\"_\\[\\]\\*\\(\\)\\.\\-]+)\\)[a-z0-9'\"_\\[\\]\\*\\(\\)\\.\\-]*",
          2)
}

bindingset[s]
string getAJsonReferenceAccessPath(string s, int offset) {
  // We use `regexpFind` to obtain *all* matches of `${{...}}`,
  // not just the last (greedy match) or first (reluctant match).
  result =
    s.trim()
        .regexpFind("(?i)(from|to)json\\([a-z0-9'\"_\\[\\]\\*\\(\\)\\.\\-]+\\)[a-z0-9'\"_\\[\\]\\*\\(\\)\\.\\-]*",
          _, offset)
        .regexpCapture("(?i)(from|to)json\\(([a-z0-9'\"_\\[\\]\\*\\(\\)\\.\\-]+)\\)([a-z0-9'\"_\\[\\]\\*\\(\\)\\.\\-]*)",
          3)
}

/**
 * A ${{}} expression accessing a sigcle context variable such as steps, needs, jobs, env, inputs, or matrix.
 * https://docs.github.com/en/actions/learn-github-actions/contexts#context-availability
 */
class SimpleReferenceExpressionImpl extends ExpressionImpl {
  SimpleReferenceExpressionImpl() {
    exists(getASimpleReferenceExpression(this.getFullExpression(), _))
    or
    exists(getAJsonReferenceExpression(this.getFullExpression(), _))
  }

  override string getExpression() {
    (
      result = getASimpleReferenceExpression(this.getFullExpression(), _)
      or
      exists(getAJsonReferenceExpression(this.getFullExpression(), _)) and
      result = this.getFullExpression()
    )
  }

  abstract string getFieldName();

  abstract AstNodeImpl getTarget();

  override string toString() { result = this.getFullExpression() }
}

class JsonReferenceExpressionImpl extends ExpressionImpl {
  string innerExpression;
  string accessPath;

  JsonReferenceExpressionImpl() {
    innerExpression = getAJsonReferenceExpression(this.getExpression(), _) and
    accessPath = getAJsonReferenceAccessPath(this.getExpression(), _)
  }

  string getInnerExpression() { result = innerExpression }

  string getAccessPath() { result = accessPath }
}

private string stepsCtxRegex() {
  result = wrapRegexp("steps\\.([A-Za-z0-9_-]+)\\.outputs\\.([A-Za-z0-9_-]+)")
}

private string needsCtxRegex() {
  result = wrapRegexp("needs\\.([A-Za-z0-9_-]+)\\.outputs\\.([A-Za-z0-9_-]+)")
}

private string jobsCtxRegex() {
  result = wrapRegexp("jobs\\.([A-Za-z0-9_-]+)\\.outputs\\.([A-Za-z0-9_-]+)")
}

private string envCtxRegex() { result = wrapRegexp("env\\.([A-Za-z0-9_-]+)") }

private string matrixCtxRegex() { result = wrapRegexp("matrix\\.(.+)") }

private string inputsCtxRegex() {
  result = wrapRegexp(["inputs\\.([A-Za-z0-9_-]+)", "github\\.event\\.inputs\\.([A-Za-z0-9_-]+)"])
}

private string secretsCtxRegex() { result = wrapRegexp("secrets\\.([A-Za-z0-9_-]+)") }

private string githubCtxRegex() {
  result = wrapRegexp("github\\.([A-Za-z0-9'\"_\\[\\]\\*\\(\\)\\.\\-]+)")
}

/**
 * Holds for an expression accesing the `github` context.
 * e.g. `${{ github.head_ref }}`
 */
class GitHubExpressionImpl extends SimpleReferenceExpressionImpl {
  GitHubExpressionImpl() {
    exists(string expr |
      (
        exists(getAJsonReferenceExpression(this.getExpression(), _)) and
        expr = normalizeExpr(this.getExpression()).regexpCapture("(?i)fromjson\\((.*)\\).*", 1)
        or
        exists(getASimpleReferenceExpression(this.getExpression(), _)) and
        expr = normalizeExpr(this.getExpression())
      ) and
      expr.regexpMatch(githubCtxRegex())
    )
  }

  override string getFieldName() {
    exists(string expr |
      (
        exists(getAJsonReferenceExpression(this.getExpression(), _)) and
        expr = normalizeExpr(this.getExpression()).regexpCapture("(?i)fromjson\\((.*)\\).*", 1)
        or
        exists(getASimpleReferenceExpression(this.getExpression(), _)) and
        expr = normalizeExpr(this.getExpression())
      ) and
      result = expr.regexpCapture(githubCtxRegex(), 1)
    )
  }

  override AstNodeImpl getTarget() { none() }
}

/**
 * Holds for an expression accesing the `secrets` context.
 * e.g. `${{ secrets.FOO }}`
 */
class SecretsExpressionImpl extends SimpleReferenceExpressionImpl {
  string fieldName;

  SecretsExpressionImpl() {
    exists(string expr |
      (
        exists(getAJsonReferenceExpression(this.getExpression(), _)) and
        expr = normalizeExpr(this.getExpression()).regexpCapture("(?i)fromjson\\((.*)\\).*", 1)
        or
        exists(getASimpleReferenceExpression(this.getExpression(), _)) and
        expr = normalizeExpr(this.getExpression())
      ) and
      expr.regexpMatch(secretsCtxRegex()) and
      fieldName = expr.regexpCapture(secretsCtxRegex(), 1)
    )
  }

  override string getFieldName() { result = fieldName }

  override AstNodeImpl getTarget() { none() }
}

/**
 * Holds for an expression accesing the `steps` context.
 * https://docs.github.com/en/actions/learn-github-actions/contexts#context-availability
 * e.g. `${{ steps.changed-files.outputs.all_changed_files }}`
 */
class StepsExpressionImpl extends SimpleReferenceExpressionImpl {
  string stepId;
  string fieldName;

  StepsExpressionImpl() {
    exists(string expr |
      (
        exists(getAJsonReferenceExpression(this.getExpression(), _)) and
        expr = normalizeExpr(this.getExpression()).regexpCapture("(?i)(from|to)json\\((.*)\\).*", 2)
        or
        exists(getASimpleReferenceExpression(this.getExpression(), _)) and
        expr = normalizeExpr(this.getExpression())
      ) and
      expr.regexpMatch(stepsCtxRegex()) and
      stepId = expr.regexpCapture(stepsCtxRegex(), 1) and
      fieldName = expr.regexpCapture(stepsCtxRegex(), 2)
    )
  }

  override string getFieldName() { result = fieldName }

  override AstNodeImpl getTarget() {
    (
      this.getEnclosingJob() = result.getEnclosingJob()
      or
      exists(CompositeActionImpl a |
        a.getAChildNode*() = this and
        a.getAChildNode*() = result
      )
    ) and
    result.(StepImpl).getId() = stepId
  }

  string getStepId() { result = stepId }
}

/**
 * Holds for an expression accesing the `needs` context.
 * https://docs.github.com/en/actions/learn-github-actions/contexts#context-availability
 * e.g. `${{ needs.job1.outputs.foo}}`
 */
class NeedsExpressionImpl extends SimpleReferenceExpressionImpl {
  JobImpl neededJob;
  string fieldName;

  NeedsExpressionImpl() {
    exists(string expr |
      (
        exists(getAJsonReferenceExpression(this.getExpression(), _)) and
        expr = normalizeExpr(this.getExpression()).regexpCapture("(?i)(from|to)json\\((.*)\\).*", 2)
        or
        exists(getASimpleReferenceExpression(this.getExpression(), _)) and
        expr = normalizeExpr(this.getExpression())
      ) and
      expr.regexpMatch(needsCtxRegex()) and
      fieldName = expr.regexpCapture(needsCtxRegex(), 2) and
      neededJob.getId() = expr.regexpCapture(needsCtxRegex(), 1) and
      (
        this.getEnclosingJob().getANeededJob() = neededJob or
        this.getEnclosingJob() = neededJob
      )
    )
  }

  string getNeededJobId() { result = neededJob.getId() }

  override string getFieldName() { result = fieldName }

  override AstNodeImpl getTarget() {
    (
      this.getEnclosingJob().getANeededJob() = neededJob or
      this.getEnclosingJob() = neededJob
    ) and
    (
      // regular jobs
      neededJob.getOutputs() = result
      or
      // reusable workflow calling jobs
      neededJob.(ExternalJobImpl) = result
    )
  }
}

/**
 * Holds for an expression accesing the `jobs` context.
 * https://docs.github.com/en/actions/learn-github-actions/contexts#context-availability
 * e.g. `${{ jobs.job1.outputs.foo}}` (within reusable workflows)
 */
class JobsExpressionImpl extends SimpleReferenceExpressionImpl {
  string jobId;
  string fieldName;

  JobsExpressionImpl() {
    exists(string expr |
      (
        exists(getAJsonReferenceExpression(this.getExpression(), _)) and
        expr = normalizeExpr(this.getExpression()).regexpCapture("(?i)(from|to)json\\((.*)\\).*", 2)
        or
        exists(getASimpleReferenceExpression(this.getExpression(), _)) and
        expr = normalizeExpr(this.getExpression())
      ) and
      expr.regexpMatch(jobsCtxRegex()) and
      jobId = expr.regexpCapture(jobsCtxRegex(), 1) and
      fieldName = expr.regexpCapture(jobsCtxRegex(), 2)
    )
  }

  override string getFieldName() { result = fieldName }

  override AstNodeImpl getTarget() {
    exists(JobImpl job |
      job.getId() = jobId and
      job.getLocation().getFile() = this.getLocation().getFile() and
      job.getOutputs() = result
    )
  }
}

/**
 * Holds for an expression the `inputs` context.
 * https://docs.github.com/en/actions/learn-github-actions/contexts#context-availability
 * e.g. `${{ inputs.foo }}`
 */
class InputsExpressionImpl extends SimpleReferenceExpressionImpl {
  string fieldName;

  InputsExpressionImpl() {
    normalizeExpr(this.getExpression()).regexpMatch(inputsCtxRegex()) and
    fieldName = normalizeExpr(this.getExpression()).regexpCapture(inputsCtxRegex(), 1)
  }

  override string getFieldName() { result = fieldName }

  override AstNodeImpl getTarget() {
    result.getLocation().getFile() = this.getLocation().getFile() and
    (
      exists(ReusableWorkflowImpl w | w.getInput(fieldName) = result)
      or
      exists(CompositeActionImpl a | a.getInput(fieldName) = result)
    )
  }
}

/**
 * Holds for an expression accesing the `env` context.
 * https://docs.github.com/en/actions/learn-github-actions/contexts#context-availability
 * e.g. `${{ env.foo }}`
 */
class EnvExpressionImpl extends SimpleReferenceExpressionImpl {
  string fieldName;

  EnvExpressionImpl() {
    exists(string expr |
      (
        exists(getAJsonReferenceExpression(this.getExpression(), _)) and
        expr = normalizeExpr(this.getExpression()).regexpCapture("(?i)(from|to)json\\((.*)\\).*", 2)
        or
        exists(getASimpleReferenceExpression(this.getExpression(), _)) and
        expr = normalizeExpr(this.getExpression())
      ) and
      expr.regexpMatch(envCtxRegex()) and
      fieldName = expr.regexpCapture(envCtxRegex(), 1)
    )
  }

  override string getFieldName() { result = fieldName }

  override AstNodeImpl getTarget() {
    exists(AstNodeImpl s |
      s.getInScopeEnvVarExpr(fieldName) = result and
      s.getAChildNode*() = this
    )
    or
    // Some Run steps may store taint in the enclosing job so we need to check the enclosing job
    result = this.getEnclosingJob()
  }
}

/**
 * Holds for an expression accesing the `matrix` context.
 * https://docs.github.com/en/actions/learn-github-actions/contexts#context-availability
 * e.g. `${{ matrix.foo }}`
 */
class MatrixExpressionImpl extends SimpleReferenceExpressionImpl {
  string fieldAccess;

  MatrixExpressionImpl() {
    exists(string expr |
      (
        exists(getAJsonReferenceExpression(this.getExpression(), _)) and
        expr = normalizeExpr(this.getExpression()).regexpCapture("(?i)(from|to)json\\((.*)\\).*", 2)
        or
        exists(getASimpleReferenceExpression(this.getExpression(), _)) and
        expr = normalizeExpr(this.getExpression())
      ) and
      expr.regexpMatch(matrixCtxRegex()) and
      fieldAccess = expr.regexpCapture(matrixCtxRegex(), 1)
    )
  }

  override string getFieldName() { result = fieldAccess }

  override AstNodeImpl getTarget() {
    result = this.getEnclosingWorkflow().getStrategy().getMatrixVarExpr(fieldAccess) or
    result = this.getEnclosingJob().getStrategy().getMatrixVarExpr(fieldAccess)
  }

  string getLiteralValues() {
    exists(StrategyImpl s, MatrixAccessPathImpl p, ScalarValueImpl v |
      (s = this.getEnclosingJob().getStrategy() or s = this.getEnclosingWorkflow().getStrategy()) and
      p.toString() = fieldAccess and
      (
        resolveMatrixAccessPath(s.getMatrix(), p).getNode(_) = v.getNode()
        or
        resolveMatrixAccessPath(
          s.getMatrix().lookup("include").(YamlSequence).getElementNode(_),
          p
        ).getNode(_) = v.getNode()
      ) and
      // Exclude values containing matrix expressions to avoid recursion
      not exists(MatrixExpressionImpl e | e.getParentNode() = v) and
      result = v.getValue()
    )
  }
}

bindingset[accessPath]
string explodeAccessPath(string accessPath) {
  result = accessPath or
  result = accessPath.suffix(accessPath.indexOf(".") + 1) or
  result = accessPath.prefix(accessPath.indexOf("."))
}

private newtype TAccessPath =
  TMatrixAccessPathNode(string accessPath) {
    exists(MatrixExpressionImpl e | accessPath = explodeAccessPath(e.getFieldName()))
  }

class MatrixAccessPathImpl extends TMatrixAccessPathNode {
  string accessPath;

  MatrixAccessPathImpl() { this = TMatrixAccessPathNode(accessPath) }

  string toString() { result = accessPath }
}

private YamlMappingLikeNode resolveMatrixAccessPath(
  // https://docs.github.com/en/actions/using-jobs/using-a-matrix-for-your-jobs#expanding-or-adding-matrix-configurations
  YamlMappingLikeNode root, MatrixAccessPathImpl accessPath
) {
  // access path contains no dots. eg: "os"
  result = root.getNode(accessPath.toString())
  or
  // access path contains dots. eg: "plaform.os"
  exists(MatrixAccessPathImpl first, MatrixAccessPathImpl rest, YamlMappingLikeNode newRoot |
    first.toString() = accessPath.toString().splitAt(".", 0) and
    rest.toString() = accessPath.toString().suffix(first.toString().length() + 1) and
    newRoot = root.getNode(first.toString()) and
    if newRoot instanceof YamlSequence
    then result = resolveMatrixAccessPath(newRoot.(YamlSequence).getElement(_), rest)
    else result = resolveMatrixAccessPath(newRoot, rest)
  )
}

class Comment = YamlComment;
