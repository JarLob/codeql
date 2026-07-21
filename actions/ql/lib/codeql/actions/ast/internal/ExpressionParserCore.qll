private import Ast

private string epsilon() { result = "" }

private string grammarText() {
  result =
    "Start ::= _Formula\n" + "_Formula ::= _Or\n" + "_Or ::= OrExpression\n" + "_Or ::= _And\n" +
      "OrExpression ::= _Or _OrOperator _And\n" + "_OrOperator ::= '||'\n" +
      "_And ::= AndExpression\n" + "_And ::= _Equality\n" +
      "AndExpression ::= _And _AndOperator _Equality\n" + "_AndOperator ::= '&&'\n" +
      "_Equality ::= EqualityExpression\n" + "_Equality ::= _Comparison\n" +
      "EqualityExpression ::= _Equality _EqualityOperator _Comparison\n" +
      "_EqualityOperator ::= '=='\n" + "_EqualityOperator ::= '!='\n" +
      "_Comparison ::= ComparisonExpression\n" + "_Comparison ::= _Unary\n" +
      "ComparisonExpression ::= _Comparison _ComparisonOperator _Unary\n" +
      "_ComparisonOperator ::= '>='\n" + "_ComparisonOperator ::= '<='\n" +
      "_ComparisonOperator ::= '>'\n" + "_ComparisonOperator ::= '<'\n" +
      "_Unary ::= NotExpression\n" + "_Unary ::= _Postfix\n" +
      "NotExpression ::= _NotOperator _Unary\n" + "_NotOperator ::= '!'\n" +
      "_Postfix ::= AccessExpression\n" + "_Postfix ::= _Primary\n" +
      "AccessExpression ::= _Postfix _Accessor\n" + "_Accessor ::= PropertyAccess\n" +
      "_Accessor ::= WildcardAccess\n" + "_Accessor ::= IndexAccess\n" +
      "PropertyAccess ::= '.' Identifier\n" + "WildcardAccess ::= '.' '*'\n" +
      "IndexAccess ::= '[' _Formula ']'\n" + "_Primary ::= FunctionCall\n" +
      "_Primary ::= BooleanLiteral\n" + "_Primary ::= NullLiteral\n" +
      "_Primary ::= NumberLiteral\n" + "_Primary ::= StringLiteral\n" + "_Primary ::= Identifier\n" +
      "_Primary ::= '(' _Formula ')'\n" + "FunctionCall ::= Identifier '(' ')'\n" +
      "FunctionCall ::= Identifier '(' _Arguments ')'\n" +
      "_Arguments ::= _Arguments ',' _Formula\n" + "_Arguments ::= _Formula\n" +
      "BooleanLiteral ::= 'true'\n" + "BooleanLiteral ::= 'false'\n" + "NullLiteral ::= 'null'\n" +
      "NumberLiteral ::= r'0x[0-9a-fA-F]+'\n" + "NumberLiteral ::= r'0o[0-7]+'\n" +
      "NumberLiteral ::= r'[+-]?([0-9]+(\\.[0-9]*)?|\\.[0-9]+)([eE][+-]?[0-9]+)?'\n" +
      "NumberLiteral ::= r'[+-]?Infinity'\n" +
      "StringLiteral ::= r'\\x27([^\\x27]|\\x27\\x27)*\\x27'\n" +
      "Identifier ::= r'[A-Za-z_][A-Za-z0-9_-]*'\n" + "_Space ::= r'\\s+'"
}

private string grammarLine(int i) { result = grammarText().splitAt("\n", i) }

private predicate rule(string lhs, string rhs, int priority) {
  exists(string line |
    line = grammarLine(priority) and
    lhs = line.splitAt(" ::= ", 0) and
    rhs = line.splitAt(" ::= ", 1)
  )
}

private string extra() { result = "_Space" }

bindingset[s]
private string getStringToken(string s) {
  s.charAt(0) = "'" and result = s.substring(1, s.length() - 1)
}

bindingset[s]
private string getRegexToken(string s) {
  s.charAt(0) = "r" and result = s.substring(2, s.length() - 1)
}

private predicate validIndex(string lhs, string rhs, int index, int priority) {
  rule(lhs, rhs, priority) and
  if rhs = epsilon()
  then index = 0
  else index in [0 .. max(int i | exists(rhs.splitAt(" ", i)) | i) + 1]
}

private string rhsPart(string lhs, string rhs, int index) {
  validIndex(lhs, rhs, index, _) and result = rhs.splitAt(" ", index)
}

private predicate validExtraIndex(string lhs, string rhs, int index, string e) {
  validIndex(lhs, rhs, index, _) and
  e = extra() and
  not rhsPart(lhs, rhs, index - 1) = e and
  not rhsPart(lhs, rhs, index) = e and
  (
    lhs = startSymbol()
    or
    index != 0 and validIndex(lhs, rhs, index + 1, _)
  )
}

private string startSymbol() { result = "Start" }

private string leftCorner(string nonterminal) { result = rhsPart(nonterminal, _, 0) }

private newtype TProduction =
  TGrammarProduction(string lhs, string rhs, int index, int priority) {
    validIndex(lhs, rhs, index, priority)
  } or
  TTokenProduction(string token, int index) {
    index in [0, 1] and
    token = any(rhsPart(_, _, _)) and
    (exists(getRegexToken(token)) or exists(getStringToken(token)))
  }

abstract class Production extends TProduction {
  abstract predicate isComplete();

  abstract predicate isPrediction();

  abstract predicate isStartItem();

  abstract predicate isHidden();

  abstract int getPriority();

  abstract string getLhs();

  abstract string toString();
}

class TokenProduction extends TTokenProduction, Production {
  string token;
  int index;

  TokenProduction() { this = TTokenProduction(token, index) }

  override string getLhs() { result = token }

  override predicate isComplete() { index = 1 }

  override predicate isPrediction() { index = 0 }

  override predicate isStartItem() { none() }

  override predicate isHidden() { any() }

  override int getPriority() { result = 0 }

  TokenProduction asPrediction() { result.getLhs() = this.getLhs() and result.isPrediction() }

  override string toString() { result = token }
}

class GrammarProduction extends TGrammarProduction, Production {
  string lhs;
  string rhs;
  int index;
  int priority;

  GrammarProduction() { this = TGrammarProduction(lhs, rhs, index, priority) }

  string getRhsPart(int i) { rhs != epsilon() and result = rhs.splitAt(" ", i) }

  override predicate isComplete() { not exists(this.getNextPart()) }

  override predicate isStartItem() { lhs = startSymbol() and index = 0 }

  predicate isExtraAllowed(string e) { validExtraIndex(lhs, rhs, index, e) }

  override string getLhs() { result = lhs }

  string getRhs() { result = rhs }

  int getIndex() { result = index }

  override predicate isPrediction() { index = 0 }

  override int getPriority() { result = priority }

  override predicate isHidden() { lhs.charAt(0) = "_" }

  GrammarProduction getPredecessor() {
    result.getLhs() = lhs and result.getRhs() = rhs and result.getIndex() = index - 1
  }

  string getNextPart() { result = this.getRhsPart(index) }

  string getPreviousPart() { result = this.getRhsPart(index - 1) }

  override string toString() { result = lhs + " ::= " + rhs + " @ " + index.toString() }
}

private predicate predictRhsPart(ExpressionImpl e, string part, int start) {
  exists(GrammarProduction prod |
    parserItem(e, prod, _, start, _) and
    (part = prod.getNextPart() or prod.isExtraAllowed(part))
  )
}

private predicate bottomUpPrediction(ExpressionImpl e, GrammarProduction prod, int start) {
  exists(string predictor, Production completed |
    predictRhsPart(e, predictor, start) and
    prod.getLhs() = leftCorner*(predictor) and
    prod.isPrediction() and
    prod.getNextPart() = completed.getLhs() and
    parserItem(e, completed, start, _, _)
  )
}

private predicate predictTerminal(ExpressionImpl e, TokenProduction prod, int start) {
  exists(string predictor |
    predictRhsPart(e, predictor, start) and
    prod.getLhs() = leftCorner*(predictor) and
    prod.isPrediction()
  )
}

private predicate scan(ExpressionImpl e, TokenProduction prod, int start, int end) {
  prod.isComplete() and
  predictTerminal(e, prod.asPrediction(), start) and
  (
    exists(string token | token = getStringToken(prod.getLhs()) |
      token = e.getExpression().substring(start, end) and end = token.length() + start
    )
    or
    exists(string regex, string match | regex = getRegexToken(prod.getLhs()) |
      match = e.getExpression().suffix(start).regexpFind(regex, _, 0) and
      end = match.length() + start
    )
  )
}

private predicate completion(ExpressionImpl e, Production prod, int start, int end, int trimmedEnd) {
  exists(Production inner, int middle |
    inner.isComplete() and
    prod.(GrammarProduction).getPreviousPart() = inner.getLhs() and
    parserItem(e, prod.(GrammarProduction).getPredecessor(), start, middle, _) and
    parserItem(e, inner, middle, end, _) and
    trimmedEnd = end
  )
}

private predicate extraCompletion(
  ExpressionImpl e, Production prod, int start, int end, int trimmedEnd
) {
  exists(GrammarProduction extraProd, int middle |
    extraProd.isComplete() and
    prod.(GrammarProduction).isExtraAllowed(extraProd.getLhs()) and
    parserItem(e, prod, start, middle, trimmedEnd) and
    parserItem(e, extraProd, middle, end, _)
  )
}

predicate parserItem(ExpressionImpl e, Production prod, int start, int end, int trimmedEnd) {
  start = 0 and
  end = start and
  trimmedEnd = end and
  prod.isStartItem() and
  exists(e)
  or
  scan(e, prod, start, end) and trimmedEnd = end
  or
  bottomUpPrediction(e, prod, start) and end = start and trimmedEnd = end
  or
  completion(e, prod, start, end, trimmedEnd)
  or
  extraCompletion(e, prod, start, end, trimmedEnd)
}

private newtype TParserItem =
  TItemNode(ExpressionImpl e, Production prod, int start, int end, int trimmedEnd) {
    parserItem(e, prod, start, end, trimmedEnd)
  }

class ItemNode extends TItemNode {
  ExpressionImpl e;
  Production prod;
  int start;
  int end;
  int trimmedEnd;

  ItemNode() { this = TItemNode(e, prod, start, end, trimmedEnd) }

  ExpressionImpl getExpression() { result = e }

  Production getProduction() { result = prod }

  int getStart() { result = start }

  int getEnd() { result = end }

  int getTrimmedEnd() { result = trimmedEnd }

  string getText() { result = e.getExpression().substring(start, end) }

  predicate isVisible() { prod.getLhs() = startSymbol() or not prod.isHidden() }

  predicate isTopNode() {
    start = 0 and end = e.getExpression().length() and prod.getLhs() = startSymbol()
  }

  private predicate getNextSpineAndChild(ItemNode left, ItemNode right) {
    left.getExpression() = e and
    right.getExpression() = e and
    left.getProduction() = prod.(GrammarProduction).getPredecessor() and
    left.getStart() = start and
    left.getEnd() = right.getStart() and
    right.getProduction().isComplete() and
    right.getProduction().getLhs() = prod.(GrammarProduction).getPreviousPart() and
    right.getEnd() = trimmedEnd and
    right = bestMatch(e, prod.(GrammarProduction).getPreviousPart(), start, trimmedEnd, this)
  }

  ItemNode getARawChild() {
    this.getNextSpineAndChild(_, result)
    or
    exists(ItemNode predecessor |
      this.getNextSpineAndChild(predecessor, _) and result = predecessor.getARawChild()
    )
  }

  ItemNode getAVisibleChild() {
    result = this.getARawChild() and result.isVisible()
    or
    exists(ItemNode child |
      child = this.getARawChild() and not child.isVisible() and result = child.getAVisibleChild()
    )
  }

  ItemNode getVisibleChild(int i) {
    result =
      rank[i + 1](ItemNode child |
        child = this.getAVisibleChild()
      |
        child order by child.getStart(), child.getEnd(), child.getProduction().getPriority()
      )
  }

  predicate isInSyntaxTree() {
    exists(ItemNode root | root.isTopNode() and this = root.getARawChild*())
  }

  string toString() { result = prod.toString() + " [" + start + ", " + end + "]" }
}

private ItemNode bestMatch(ExpressionImpl e, string part, int start, int end, ItemNode after) {
  result =
    min(ItemNode before, ItemNode child |
      predecessorCandidate(e, part, start, end, before, child, after)
    |
      child order by child.getProduction().getPriority(), child.getStart()
    )
}

private predicate predecessorCandidate(
  ExpressionImpl e, string part, int start, int end, ItemNode before, ItemNode child, ItemNode after
) {
  before.getExpression() = e and
  child.getExpression() = e and
  after.getExpression() = e and
  after.getStart() = start and
  after.getTrimmedEnd() = end and
  after.getProduction().(GrammarProduction).getPredecessor() = before.getProduction() and
  after.getProduction().(GrammarProduction).getPreviousPart() = part and
  child.getProduction().getLhs() = part and
  child.getProduction().isComplete() and
  child.getEnd() = end and
  before.getStart() = start and
  before.getEnd() = child.getStart() and
  before.getProduction().(GrammarProduction).getNextPart() = part
}
