private import Ast
private import ExpressionParserCore
private import Yaml

/** Gets the exclusive end offset of the access-chain part starting at `start`. */
bindingset[expression, start]
pragma[inline_late]
private int getSimpleAccessPartEnd(ExpressionImpl expression, int start) {
  start < expression.getFullExpression().length() and
  result =
    start +
      min([
            expression.getFullExpression().suffix(start).indexOf("."),
            expression.getFullExpression().length() - start
          ]
      )
}

private predicate getASimpleAccessPart(ExpressionImpl expression, int start, int end) {
  start = 0 and end = getSimpleAccessPartEnd(expression, start)
  or
  exists(int previousStart |
    getASimpleAccessPart(expression, previousStart, start - 1) and
    start > 0 and
    end = getSimpleAccessPartEnd(expression, start)
  )
}

/** A generic parser node, or a directly represented simple access-chain node. */
private newtype TExpressionNode =
  TParsedExpressionNode(ItemNode item) { item.isInSyntaxTree() and item.isVisible() } or
  TDirectExpressionRoot(ExpressionImpl expression) { isSimpleAccessExpression(expression) } or
  TDirectAccessExpression(ExpressionImpl expression, int end) {
    isSimpleAccessExpression(expression) and
    exists(int start | getASimpleAccessPart(expression, start, end) and start > 0)
  } or
  TDirectIdentifierExpression(ExpressionImpl expression, int start, int end) {
    isSimpleAccessExpression(expression) and
    getASimpleAccessPart(expression, start, end) and
    expression.getFullExpression().substring(start, end) != "*"
  } or
  TDirectPropertyAccessExpression(ExpressionImpl expression, int start, int end) {
    isSimpleAccessExpression(expression) and
    start >= 0 and
    getASimpleAccessPart(expression, start + 1, end) and
    expression.getFullExpression().substring(start + 1, end) != "*"
  } or
  TDirectWildcardAccessExpression(ExpressionImpl expression, int start, int end) {
    isSimpleAccessExpression(expression) and
    start >= 0 and
    getASimpleAccessPart(expression, start + 1, end) and
    expression.getFullExpression().substring(start + 1, end) = "*"
  }

class ExpressionNodeImpl extends TExpressionNode {
  ItemNode getParserItem() { this = TParsedExpressionNode(result) }

  ExpressionImpl getExpression() {
    result = this.getParserItem().getExpression()
    or
    this = TDirectExpressionRoot(result)
    or
    this = TDirectAccessExpression(result, _)
    or
    this = TDirectIdentifierExpression(result, _, _)
    or
    this = TDirectPropertyAccessExpression(result, _, _)
    or
    this = TDirectWildcardAccessExpression(result, _, _)
  }

  string getRawKind() {
    (
      if this.getParserItem().isTopNode()
      then result = "root"
      else result = this.getParserItem().getProduction().getLhs()
    )
    or
    this = TDirectExpressionRoot(_) and result = "root"
    or
    this = TDirectAccessExpression(_, _) and result = "AccessExpression"
    or
    this = TDirectIdentifierExpression(_, 0, _) and result = "Identifier"
    or
    exists(ExpressionImpl expression, int start, int end |
      this = TDirectIdentifierExpression(expression, start, end) and
      start > 0 and
      result = "PropertyIdentifier"
    )
    or
    this = TDirectPropertyAccessExpression(_, _, _) and result = "PropertyAccess"
    or
    this = TDirectWildcardAccessExpression(_, _, _) and result = "WildcardAccess"
  }

  predicate isTopNode() {
    this.getParserItem().isTopNode()
    or
    this = TDirectExpressionRoot(_)
  }

  ExpressionNodeImpl getChild(int i) {
    result = TParsedExpressionNode(this.getParserItem().getVisibleChild(i))
    or
    exists(ExpressionImpl expression |
      i = 0 and
      this = TDirectExpressionRoot(expression) and
      (
        not exists(int start, int end | getASimpleAccessPart(expression, start, end) and start > 0) and
        result = TDirectIdentifierExpression(expression, 0, expression.getFullExpression().length())
        or
        exists(int start, int end | getASimpleAccessPart(expression, start, end) and start > 0) and
        result = TDirectAccessExpression(expression, expression.getFullExpression().length())
      )
    )
    or
    exists(ExpressionImpl expression, int start, int end, int previousStart |
      this = TDirectAccessExpression(expression, end) and
      getASimpleAccessPart(expression, start, end) and
      start > 0 and
      getASimpleAccessPart(expression, previousStart, start - 1) and
      (
        i = 0 and
        (
          previousStart = 0 and
          result = TDirectIdentifierExpression(expression, previousStart, start - 1)
          or
          previousStart > 0 and
          result = TDirectAccessExpression(expression, start - 1)
        )
        or
        i = 1 and
        (
          expression.getFullExpression().substring(start, end) != "*" and
          result = TDirectPropertyAccessExpression(expression, start - 1, end)
          or
          expression.getFullExpression().substring(start, end) = "*" and
          result = TDirectWildcardAccessExpression(expression, start - 1, end)
        )
      )
    )
    or
    exists(ExpressionImpl expression, int start, int end |
      i = 0 and
      this = TDirectPropertyAccessExpression(expression, start, end) and
      result = TDirectIdentifierExpression(expression, start + 1, end)
    )
  }

  ExpressionNodeImpl getAChild() { result = this.getChild(_) }

  ExpressionNodeImpl getParent() { result.getAChild() = this }

  string getKind() { result = this.getRawKind() }

  int getStartOffset() {
    result = this.getParserItem().getStart()
    or
    this = TDirectExpressionRoot(_) and result = 0
    or
    this = TDirectAccessExpression(_, _) and result = 0
    or
    this = TDirectIdentifierExpression(_, result, _)
    or
    this = TDirectPropertyAccessExpression(_, result, _)
    or
    this = TDirectWildcardAccessExpression(_, result, _)
  }

  int getEndOffset() {
    result = this.getParserItem().getEnd()
    or
    exists(ExpressionImpl expression |
      this = TDirectExpressionRoot(expression) and result = expression.getFullExpression().length()
    )
    or
    this = TDirectAccessExpression(_, result)
    or
    this = TDirectIdentifierExpression(_, _, result)
    or
    this = TDirectPropertyAccessExpression(_, _, result)
    or
    this = TDirectWildcardAccessExpression(_, _, result)
  }

  string getText() {
    result = this.getParserItem().getText()
    or
    not exists(this.getParserItem()) and
    result = this.getExpression().getFullExpression().substring(this.getStartOffset(), this.getEndOffset())
  }

  predicate hasLocationInfo(string path, int sl, int sc, int el, int ec) {
    this.getExpression()
        .expressionNodeLocation(this.getStartOffset(), this.getEndOffset(), path, sl, sc, el, ec)
  }

  predicate hasExactSourceLocation() { this.getExpression().expressionNodeLocationIsExact() }

  int getRunnerDepth() {
    exists(ItemNode root | root = this.getParserItem() |
      result =
        max(int depth |
          exists(ItemNode descendant | runnerDescendantDepth(root, descendant, depth))
        |
          depth
        )
    )
    or
    not exists(this.getParserItem()) and
    result = count(int start, int end | getASimpleAccessPart(this.getExpression(), start, end))
  }

  string toString() { result = this.getKind() + "(" + this.getText() + ")" }
}

private ExpressionNodeImpl getALogicalOperand(BinaryExpressionImpl binary) {
  exists(ExpressionNodeImpl direct | direct = [binary.getLeftOperand(), binary.getRightOperand()] |
    if
      binary.getOperator() = ["&&", "||"] and
      direct instanceof BinaryExpressionImpl and
      direct.(BinaryExpressionImpl).getOperator() = binary.getOperator()
    then result = getALogicalOperand(direct.(BinaryExpressionImpl))
    else result = direct
  )
}

private ExpressionNodeImpl getARunnerChild(ExpressionNodeImpl parent) {
  parent instanceof BinaryExpressionImpl and
  parent.(BinaryExpressionImpl).getOperator() = ["&&", "||"] and
  result = getALogicalOperand(parent.(BinaryExpressionImpl))
  or
  parent instanceof BinaryExpressionImpl and
  parent.(BinaryExpressionImpl).getOperator() != ["&&", "||"] and
  result =
    [
      parent.(BinaryExpressionImpl).getLeftOperand(),
      parent.(BinaryExpressionImpl).getRightOperand()
    ]
  or
  parent instanceof UnaryExpressionImpl and
  result = parent.(UnaryExpressionImpl).getOperand()
  or
  parent instanceof FunctionCallExpressionImpl and
  result = parent.(FunctionCallExpressionImpl).getArgument(_)
  or
  parent instanceof AccessExpressionImpl and
  (
    result = parent.(AccessExpressionImpl).getBase()
    or
    parent.(AccessExpressionImpl).getAccessor() instanceof IndexAccessExpressionImpl and
    result = parent.(AccessExpressionImpl).getAccessor().(IndexAccessExpressionImpl).getIndex()
    or
    not parent.(AccessExpressionImpl).getAccessor() instanceof IndexAccessExpressionImpl and
    result = parent.(AccessExpressionImpl).getAccessor()
  )
}

private ItemNode getARunnerParserChild(ItemNode parent) {
  exists(ExpressionNodeImpl parentNode, ExpressionNodeImpl childNode |
    parentNode = TParsedExpressionNode(parent) and
    childNode = getARunnerChild(parentNode) and
    childNode = TParsedExpressionNode(result)
  )
}

private predicate runnerDescendantDepth(ItemNode root, ItemNode node, int depth) {
  node = root and depth = 1
  or
  exists(ItemNode parent, int parentDepth |
    node = getARunnerParserChild(parent) and
    runnerDescendantDepth(root, parent, parentDepth) and
    depth = parentDepth + 1
  )
}

private predicate hasValidWellKnownFunctionArity(FunctionCallExpressionImpl call) {
  exists(string name, int argumentCount |
    name = call.getCallee().getName().toLowerCase() and
    argumentCount = count(call.getArgument(_))
  |
    name = "case" and argumentCount in [3 .. 255] and argumentCount % 2 = 1
    or
    name = ["contains", "endswith", "startswith"] and argumentCount = 2
    or
    name = ["fromjson", "tojson"] and argumentCount = 1
    or
    name = "join" and argumentCount in [1, 2]
    or
    name = "format" and argumentCount in [1 .. 255]
    or
    not name =
      ["case", "contains", "endswith", "startswith", "fromjson", "tojson", "join", "format"]
  )
}

class ExpressionRootImpl extends ExpressionNodeImpl {
  ExpressionRootImpl() {
    this.isTopNode() and
    this.getChild(0).getRunnerDepth() <= 50 and
    forall(FunctionCallExpressionImpl call | call.getExpression() = this.getExpression() |
      hasValidWellKnownFunctionArity(call)
    )
  }
}

class BinaryExpressionImpl extends ExpressionNodeImpl {
  BinaryExpressionImpl() {
    this.getKind() = ["OrExpression", "AndExpression", "EqualityExpression", "ComparisonExpression"]
  }

  ExpressionNodeImpl getLeftOperand() { result = this.getChild(0) }

  ExpressionNodeImpl getRightOperand() { result = this.getChild(1) }

  string getOperator() {
    exists(ItemNode operator |
      operator = this.getParserItem().getARawChild() and
      operator.getProduction().getLhs() =
        ["_OrOperator", "_AndOperator", "_EqualityOperator", "_ComparisonOperator"] and
      result = operator.getText().trim()
    )
  }
}

class UnaryExpressionImpl extends ExpressionNodeImpl {
  UnaryExpressionImpl() { this.getKind() = "NotExpression" }

  ExpressionNodeImpl getOperand() { result = this.getChild(0) }

  string getOperator() { result = "!" }
}

class IdentifierExpressionImpl extends ExpressionNodeImpl {
  IdentifierExpressionImpl() { this.getRawKind() = ["Identifier", "PropertyIdentifier"] }

  override string getKind() { result = "Identifier" }

  string getName() { result = this.getText() }
}

class FunctionCallExpressionImpl extends ExpressionNodeImpl {
  FunctionCallExpressionImpl() { this.getKind() = "FunctionCall" }

  IdentifierExpressionImpl getCallee() { result = this.getChild(0) }

  ExpressionNodeImpl getArgument(int i) { i >= 0 and result = this.getChild(i + 1) }
}

class AccessExpressionImpl extends ExpressionNodeImpl {
  AccessExpressionImpl() { this.getKind() = "AccessExpression" }

  ExpressionNodeImpl getBase() { result = this.getChild(0) }

  ExpressionNodeImpl getAccessor() { result = this.getChild(1) }
}

class PropertyAccessExpressionImpl extends ExpressionNodeImpl {
  PropertyAccessExpressionImpl() { this.getKind() = "PropertyAccess" }

  string getName() { result = this.getChild(0).getText() }
}

class WildcardAccessExpressionImpl extends ExpressionNodeImpl {
  WildcardAccessExpressionImpl() { this.getKind() = "WildcardAccess" }
}

class IndexAccessExpressionImpl extends ExpressionNodeImpl {
  IndexAccessExpressionImpl() { this.getKind() = "IndexAccess" }

  ExpressionNodeImpl getIndex() { result = this.getChild(0) }
}

class LiteralExpressionImpl extends ExpressionNodeImpl {
  LiteralExpressionImpl() {
    this.getKind() = ["BooleanLiteral", "NullLiteral", "NumberLiteral", "StringLiteral"]
  }

  string getValue() { result = this.getText() }
}

bindingset[node]
pragma[inline_late]
private string getParsedStringLiteralValue(ExpressionNodeImpl node) {
  node instanceof LiteralExpressionImpl and
  node.getKind() = "StringLiteral" and
  result =
    node.(LiteralExpressionImpl)
        .getValue()
        .substring(1, node.(LiteralExpressionImpl).getValue().length() - 1)
        .regexpReplaceAll("''", "'")
}

bindingset[accessor]
pragma[inline_late]
private string getParsedNamedAccessor(ExpressionNodeImpl accessor) {
  accessor instanceof PropertyAccessExpressionImpl and
  result = accessor.(PropertyAccessExpressionImpl).getName()
  or
  accessor instanceof IndexAccessExpressionImpl and
  result = getParsedStringLiteralValue(accessor.(IndexAccessExpressionImpl).getIndex())
}

bindingset[accessor]
pragma[inline_late]
private int getParsedNumericAccessor(ExpressionNodeImpl accessor) {
  accessor instanceof IndexAccessExpressionImpl and
  accessor.(IndexAccessExpressionImpl).getIndex() instanceof LiteralExpressionImpl and
  accessor.(IndexAccessExpressionImpl).getIndex().getKind() = "NumberLiteral" and
  accessor.(IndexAccessExpressionImpl).getIndex().(LiteralExpressionImpl).getValue().regexpMatch("[0-9]+") and
  result = accessor.(IndexAccessExpressionImpl).getIndex().(LiteralExpressionImpl).getValue().toInt()
}

bindingset[accessor]
pragma[inline_late]
private predicate isParsedAnyAccessor(ExpressionNodeImpl accessor) {
  accessor instanceof WildcardAccessExpressionImpl
  or
  accessor instanceof IndexAccessExpressionImpl and
  not exists(getParsedNamedAccessor(accessor)) and
  not exists(getParsedNumericAccessor(accessor))
}

bindingset[root, accessor]
pragma[inline_late]
private YamlMappingLikeNode getParsedAccessedYamlNode(
  YamlMappingLikeNode root, ExpressionNodeImpl accessor
) {
  result = root.getNode(getParsedNamedAccessor(accessor))
  or
  result = root.(YamlSequence).getElement(getParsedNumericAccessor(accessor))
  or
  isParsedAnyAccessor(accessor) and
  (
    root.(YamlMapping).maps(_, result)
    or
    result = root.(YamlSequence).getElement(_)
  )
}

bindingset[root, accessor]
pragma[inline_late]
private YamlMappingLikeNode getParsedMatrixDimensionNode(
  YamlMapping root, ExpressionNodeImpl accessor
) {
  exists(YamlScalar key |
    root.maps(key, result) and
    not key.getValue().toLowerCase() = ["include", "exclude"] and
    (
      key.getValue() = getParsedNamedAccessor(accessor)
      or
      isParsedAnyAccessor(accessor)
    )
  )
}

private YamlScalar getAParsedMatrixValueScalar(YamlMappingLikeNode value) {
  result = value
  or
  exists(YamlMapping mapping, YamlMappingLikeNode child |
    value = mapping and
    mapping.maps(_, child) and
    result = getAParsedMatrixValueScalar(child)
  )
  or
  exists(YamlSequence sequence, YamlMappingLikeNode child |
    value = sequence and
    child = sequence.getElement(_) and
    result = getAParsedMatrixValueScalar(child)
  )
}

private predicate isParsedMatrixAccess(ExpressionNodeImpl node) {
  exists(AccessExpressionImpl access, IdentifierExpressionImpl identifier |
    node = access and
    access.getBase() = identifier and
    identifier.getName().toLowerCase() = "matrix"
  )
  or
  exists(AccessExpressionImpl access |
    node = access and
    access.getBase() instanceof AccessExpressionImpl and
    isParsedMatrixAccess(access.getBase())
  )
}

private StrategyImpl getParsedMatrixStrategy(ExpressionNodeImpl reference) {
  result = reference.getExpression().getEnclosingJob().getStrategy()
  or
  result = reference.getExpression().getEnclosingWorkflow().getStrategy()
}

private YamlNode getMatrixDefinition(StrategyImpl strategy) {
  result = strategy.getNode().lookup("matrix")
}

private YamlScalar getARuntimeMatrixDefinitionScalar(StrategyImpl strategy) {
  result = getMatrixDefinition(strategy)
  or
  exists(YamlMapping matrix, YamlScalar key, YamlMappingLikeNode value |
    matrix = getMatrixDefinition(strategy) and
    matrix.maps(key, value) and
    not key.getValue().toLowerCase() = "exclude" and
    result = getAParsedMatrixValueScalar(value)
  )
}

private newtype TParsedMatrixRoot =
  TParsedMatrixDimensions(StrategyImpl strategy, YamlMapping root) {
    root = getMatrixDefinition(strategy)
  } or
  TParsedMatrixInclude(StrategyImpl strategy, YamlMapping root) {
    root =
      getMatrixDefinition(strategy)
          .(YamlMapping)
          .lookup("include")
          .(YamlSequence)
          .getElement(_)
  }

private class ParsedMatrixRoot extends TParsedMatrixRoot {
  StrategyImpl getStrategy() {
    this = TParsedMatrixDimensions(result, _) or this = TParsedMatrixInclude(result, _)
  }

  YamlMapping getNode() {
    this = TParsedMatrixDimensions(_, result) or this = TParsedMatrixInclude(_, result)
  }

  predicate containsDimensions() { this = TParsedMatrixDimensions(_, _) }

  string toString() { result = this.getNode().toString() }
}

private newtype TParsedMatrixResolution =
  TParsedMatrixDimension(YamlMappingLikeNode value) or
  TParsedMatrixValue(YamlMappingLikeNode value)

private class ParsedMatrixResolution extends TParsedMatrixResolution {
  YamlMappingLikeNode getValue() {
    this = TParsedMatrixDimension(result) or this = TParsedMatrixValue(result)
  }

  predicate isDimension() { this = TParsedMatrixDimension(_) }

  string toString() { result = this.getValue().toString() }
}

private ParsedMatrixResolution resolveParsedMatrixAccess(
  ExpressionNodeImpl node, ParsedMatrixRoot root
) {
  exists(
    AccessExpressionImpl access, IdentifierExpressionImpl identifier, YamlMappingLikeNode value
  |
    node = access and
    access.getBase() = identifier and
    identifier.getName().toLowerCase() = "matrix" and
    (
      root.containsDimensions() and
      value = getParsedMatrixDimensionNode(root.getNode(), access.getAccessor()) and
      result = TParsedMatrixDimension(value)
      or
      not root.containsDimensions() and
      value = getParsedAccessedYamlNode(root.getNode(), access.getAccessor()) and
      result = TParsedMatrixValue(value)
    )
  )
  or
  exists(
    AccessExpressionImpl access, ParsedMatrixResolution base, YamlMappingLikeNode value
  |
    node = access and
    access.getBase() instanceof AccessExpressionImpl and
    base = resolveParsedMatrixAccess(access.getBase(), root) and
    (
      base.isDimension() and
      value =
        getParsedAccessedYamlNode(
          base.getValue().(YamlSequence).getElement(_), access.getAccessor()
        )
      or
      not base.isDimension() and
      value = getParsedAccessedYamlNode(base.getValue(), access.getAccessor())
    ) and
    result = TParsedMatrixValue(value)
  )
}

/** A parsed access rooted at the GitHub Actions `matrix` context. */
class MatrixAccessExpressionImpl extends AccessExpressionImpl {
  MatrixAccessExpressionImpl() {
    isParsedMatrixAccess(this) and
    not exists(AccessExpressionImpl parent | parent.getBase() = this)
  }

  AstNodeImpl getTarget() {
    exists(StrategyImpl strategy, ParsedMatrixRoot root, ParsedMatrixResolution resolution,
      YamlScalar scalar |
      strategy = getParsedMatrixStrategy(this) and
      root.getStrategy() = strategy and
      resolution = resolveParsedMatrixAccess(this, root) and
      scalar = getAParsedMatrixValueScalar(resolution.getValue()) and
      result.(ExpressionImpl).getParentNode().getNode() = scalar
    )
    or
    exists(StrategyImpl strategy |
      strategy = getParsedMatrixStrategy(this) and
      (
        result.(ExpressionImpl).getParentNode().getNode() = getMatrixDefinition(strategy)
        or
        result.(ExpressionImpl).getParentNode().getNode() =
          getMatrixDefinition(strategy).(YamlMapping).lookup("include")
      )
    )
  }
}

/** A parsed reference to the whole GitHub Actions `matrix` context. */
class MatrixContextExpressionImpl extends IdentifierExpressionImpl {
  MatrixContextExpressionImpl() {
    this.getName().toLowerCase() = "matrix" and
    not exists(AccessExpressionImpl access | access.getBase() = this) and
    not exists(PropertyAccessExpressionImpl property | property.getChild(0) = this) and
    not exists(FunctionCallExpressionImpl call | call.getCallee() = this)
  }

  AstNodeImpl getATarget() {
    exists(StrategyImpl strategy, YamlScalar scalar |
      strategy = getParsedMatrixStrategy(this) and
      scalar = getARuntimeMatrixDefinitionScalar(strategy) and
      result.(ExpressionImpl).getParentNode().getNode() = scalar
    )
  }
}
