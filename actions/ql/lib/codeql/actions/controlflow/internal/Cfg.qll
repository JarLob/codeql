private import codeql.actions.Ast
private import codeql.controlflow.Cfg as CfgShared
private import codeql.Locations

module Completion {
  import codeql.controlflow.SuccessorType

  private newtype TCompletion =
    TSimpleCompletion() or
    TBooleanCompletion(boolean b) { b in [false, true] } or
    TReturnCompletion()

  abstract class Completion extends TCompletion {
    abstract string toString();

    predicate isValidForSpecific(AstNode e) { none() }

    predicate isValidFor(AstNode e) { this.isValidForSpecific(e) }

    abstract SuccessorType getAMatchingSuccessorType();
  }

  abstract class NormalCompletion extends Completion { }

  class SimpleCompletion extends NormalCompletion, TSimpleCompletion {
    SimpleCompletion() { this = TSimpleCompletion() }

    override string toString() { result = "SimpleCompletion" }

    override predicate isValidFor(AstNode e) { not any(Completion c).isValidForSpecific(e) }

    override DirectSuccessor getAMatchingSuccessorType() { any() }
  }

  class BooleanCompletion extends NormalCompletion, TBooleanCompletion {
    boolean value;

    BooleanCompletion() { this = TBooleanCompletion(value) }

    override string toString() { result = "BooleanCompletion(" + value + ")" }

    override predicate isValidForSpecific(AstNode e) { e instanceof If }

    override BooleanSuccessor getAMatchingSuccessorType() { result.getValue() = value }

    final boolean getValue() { result = value }
  }

  class ReturnCompletion extends Completion, TReturnCompletion {
    override string toString() { result = "ReturnCompletion" }

    override predicate isValidForSpecific(AstNode e) { none() }

    override ReturnSuccessor getAMatchingSuccessorType() { any() }
  }
}

module CfgScope {
  abstract class CfgScope extends AstNode { }

  class WorkflowScope extends CfgScope instanceof Workflow { }

  class CompositeActionScope extends CfgScope instanceof CompositeAction { }
}

private module Implementation implements CfgShared::InputSig<Location> {
  import codeql.actions.Ast
  import Completion
  import CfgScope

  predicate completionIsNormal(Completion c) { not c instanceof ReturnCompletion }

  // Not using CFG splitting, so the following are just dummy types.
  private newtype TUnit = Unit()

  additional class SplitKindBase = TUnit;

  additional class Split extends TUnit {
    abstract string toString();
  }

  predicate completionIsSimple(Completion c) { c instanceof SimpleCompletion }

  predicate completionIsValidFor(Completion c, AstNode e) { c.isValidFor(e) }

  CfgScope getCfgScope(AstNode e) {
    exists(AstNode p | p = e.getParentNode() |
      result = p
      or
      not p instanceof CfgScope and result = getCfgScope(p)
    )
  }

  additional int maxSplits() { result = 0 }

  predicate scopeFirst(CfgScope scope, AstNode e) {
    first(scope.(Workflow), e) or
    first(scope.(CompositeAction), e)
  }

  predicate scopeLast(CfgScope scope, AstNode e, Completion c) {
    last(scope.(Workflow), e, c) or
    last(scope.(CompositeAction), e, c)
  }

  SuccessorType getAMatchingSuccessorType(Completion c) { result = c.getAMatchingSuccessorType() }

  int idOfAstNode(AstNode node) { none() }

  int idOfCfgScope(CfgScope scope) { none() }
}

module CfgImpl = CfgShared::Make<Location, Implementation>;

private import CfgImpl
private import Completion
private import CfgScope

private class CompositeActionTree extends StandardPreOrderTree instanceof CompositeAction {
  override ControlFlowTree getChildNode(int i) {
    result =
      rank[i](AstNode child, Location l |
        (
          child = this.(CompositeAction).getAnInput() or
          child = this.(CompositeAction).getOutputs() or
          child = this.(CompositeAction).getRuns()
        ) and
        l = child.getLocation()
      |
        child
        order by
          l.getStartLine(), l.getStartColumn(), l.getEndColumn(), l.getEndLine(), child.toString()
      )
  }
}

private class RunsTree extends StandardPreOrderTree instanceof Runs {
  override ControlFlowTree getChildNode(int i) { result = super.getStep(i) }
}

private class WorkflowTree extends StandardPreOrderTree instanceof Workflow {
  override ControlFlowTree getChildNode(int i) {
    if this instanceof ReusableWorkflow
    then
      result =
        rank[i](AstNode child, Location l |
          (
            child = this.(ReusableWorkflow).getAnInput() or
            child = this.(ReusableWorkflow).getOutputs() or
            child = this.(ReusableWorkflow).getStrategy() or
            child = this.(ReusableWorkflow).getAJob()
          ) and
          l = child.getLocation()
        |
          child
          order by
            l.getStartLine(), l.getStartColumn(), l.getEndColumn(), l.getEndLine(), child.toString()
        )
    else
      result =
        rank[i](AstNode child, Location l |
          (
            child = super.getStrategy() or
            child = super.getAJob()
          ) and
          l = child.getLocation()
        |
          child
          order by
            l.getStartLine(), l.getStartColumn(), l.getEndColumn(), l.getEndLine(), child.toString()
        )
  }
}

private class OutputsTree extends StandardPreOrderTree instanceof Outputs {
  override ControlFlowTree getChildNode(int i) {
    result =
      rank[i](AstNode child, Location l |
        child = super.getAnOutputExpr() and l = child.getLocation()
      |
        child
        order by
          l.getStartLine(), l.getStartColumn(), l.getEndColumn(), l.getEndLine(), child.toString()
      )
  }
}

private class StrategyTree extends StandardPreOrderTree instanceof Strategy {
  override ControlFlowTree getChildNode(int i) {
    result =
      rank[i](AstNode child, Location l |
        child = super.getAMatrixVarExpr() and l = child.getLocation()
      |
        child
        order by
          l.getStartLine(), l.getStartColumn(), l.getEndColumn(), l.getEndLine(), child.toString()
      )
  }
}

abstract private class GuardedPreOrderTree extends ControlFlowTree {
  abstract If getGuard();

  abstract AstNode getBodyChild(int i);

  private ControlFlowTree getBodyChildTreeRanked(int i) {
    result =
      rank[i + 1](ControlFlowTree child, int j | child = this.getBodyChild(j) | child order by j)
  }

  private ControlFlowTree getFirstBodyChildTree() { result = this.getBodyChildTreeRanked(0) }

  private ControlFlowTree getLastBodyChildTree() {
    exists(int last |
      result = this.getBodyChildTreeRanked(last) and
      not exists(this.getBodyChildTreeRanked(last + 1))
    )
  }

  private predicate bodyLast(AstNode last, Completion c) {
    last(this.getLastBodyChildTree(), last, c)
    or
    not exists(this.getFirstBodyChildTree()) and last = this and c.isValidFor(this)
  }

  override predicate first(AstNode first) {
    first(this.getGuard(), first)
    or
    not exists(this.getGuard()) and first = this
  }

  override predicate last(AstNode last, Completion c) {
    exists(BooleanCompletion completion |
      last(this.getGuard(), last, completion) and
      completion.getValue() = false and
      c = completion
    )
    or
    this.bodyLast(last, c)
  }

  override predicate propagatesAbnormal(AstNode child) {
    child = this.getGuard() or child = this.getBodyChild(_)
  }

  override predicate succ(AstNode pred, AstNode succ, Completion c) {
    exists(BooleanCompletion completion |
      last(this.getGuard(), pred, completion) and
      completion.getValue() = true and
      c = completion and
      succ = this
    )
    or
    exists(SimpleCompletion completion |
      pred = this and
      first(this.getFirstBodyChildTree(), succ) and
      c = completion
    )
    or
    exists(int i |
      last(this.getBodyChildTreeRanked(i), pred, c) and
      not c instanceof ReturnCompletion and
      first(this.getBodyChildTreeRanked(i + 1), succ)
    )
  }
}

private class JobTree extends GuardedPreOrderTree instanceof LocalJob {
  override If getGuard() { result = this.(LocalJob).getIf() }

  override AstNode getBodyChild(int i) {
    result =
      rank[i](AstNode child, Location l |
        (
          child = this.(LocalJob).getAStep() or
          child = this.(LocalJob).getOutputs() or
          child = this.(LocalJob).getStrategy()
        ) and
        l = child.getLocation()
      |
        child
        order by
          l.getStartLine(), l.getStartColumn(), l.getEndColumn(), l.getEndLine(), child.toString()
      )
  }
}

private class ExternalJobTree extends GuardedPreOrderTree instanceof ExternalJob {
  override If getGuard() { result = this.(ExternalJob).getIf() }

  override AstNode getBodyChild(int i) {
    result =
      rank[i](AstNode child, Location l |
        (
          child = this.(ExternalJob).getArgumentExpr(_) or
          child = this.(ExternalJob).getSecretExpr(_) or
          child = this.(ExternalJob).getInScopeEnvVarExpr(_) or
          child = this.(ExternalJob).getOutputs() or
          child = this.(ExternalJob).getStrategy()
        ) and
        l = child.getLocation()
      |
        child
        order by
          l.getStartLine(), l.getStartColumn(), l.getEndColumn(), l.getEndLine(), child.toString()
      )
  }
}

private class UsesTree extends GuardedPreOrderTree instanceof UsesStep {
  override If getGuard() { result = this.(UsesStep).getIf() }

  override AstNode getBodyChild(int i) {
    result =
      rank[i](AstNode child, Location l |
        (
          child = this.(UsesStep).getArgumentExpr(_) or
          child = this.(UsesStep).getInScopeEnvVarExpr(_)
        ) and
        l = child.getLocation()
      |
        child
        order by
          l.getStartLine(), l.getStartColumn(), l.getEndColumn(), l.getEndLine(), child.toString()
      )
  }
}

private class RunTree extends GuardedPreOrderTree instanceof Run {
  override If getGuard() { result = this.(Run).getIf() }

  override AstNode getBodyChild(int i) {
    result =
      rank[i](AstNode child, Location l |
        (
          child = this.(Run).getInScopeEnvVarExpr(_) or
          child = this.(Run).getAnScriptExpr() or
          child = this.(Run).getScript()
        ) and
        l = child.getLocation()
      |
        child
        order by
          l.getStartLine(), l.getStartColumn(), l.getEndColumn(), l.getEndLine(), child.toString()
      )
  }
}

private class ScalarValueTree extends StandardPreOrderTree instanceof ScalarValue {
  override ControlFlowTree getChildNode(int i) {
    result =
      rank[i](Expression child, Location l |
        child = super.getAChildNode() and
        l = child.getLocation()
      |
        child
        order by
          l.getStartLine(), l.getStartColumn(), l.getEndColumn(), l.getEndLine(), child.toString()
      )
  }
}

private class UsesLeaf extends LeafTree instanceof Uses { }

private class InputTree extends LeafTree instanceof Input { }

private class ScalarValueLeaf extends LeafTree instanceof ScalarValue { }

private class ExpressionLeaf extends LeafTree instanceof Expression { }

private class IfLeaf extends LeafTree instanceof If { }
