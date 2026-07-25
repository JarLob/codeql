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

abstract private class BackgroundTree extends ControlFlowTree {
  abstract BackgroundStep getBackgroundStep();

  abstract AstNode getBodyChild(int i);

  private If getGuard() { result = this.getBackgroundStep().getIf() }

  private ControlFlowTree getBodyChildTree(int i) { result = this.getBodyChild(i) }

  private ControlFlowTree getFirstBodyChildTree() { result = this.getBodyChildTree(1) }

  private ControlFlowTree getLastBodyChildTree() {
    exists(int last |
      result = this.getBodyChildTree(last) and not exists(this.getBodyChildTree(last + 1))
    )
  }

  override predicate first(AstNode firstNode) {
    first(this.getGuard(), firstNode)
    or
    not exists(this.getGuard()) and firstNode = this
  }

  override predicate last(AstNode lastNode, Completion completion) {
    exists(BooleanCompletion guardCompletion |
      last(this.getGuard(), lastNode, guardCompletion) and
      guardCompletion.getValue() = false and
      completion = guardCompletion
    )
    or
    lastNode = this and completion instanceof SimpleCompletion
  }

  override predicate propagatesAbnormal(AstNode child) {
    child = this.getGuard() or child = this.getBodyChild(_)
  }

  override predicate succ(AstNode predecessor, AstNode successor, Completion completion) {
    exists(BooleanCompletion guardCompletion |
      last(this.getGuard(), predecessor, guardCompletion) and
      guardCompletion.getValue() = true and
      completion = guardCompletion and
      successor = this
    )
    or
    predecessor = this and
    completion instanceof SimpleCompletion and
    (
      first(this.getFirstBodyChildTree(), successor)
      or
      not exists(this.getFirstBodyChildTree()) and
      successor = this.getBackgroundStep().getCompletion()
    )
    or
    exists(int i |
      last(this.getBodyChildTree(i), predecessor, completion) and
      completion instanceof NormalCompletion and
      first(this.getBodyChildTree(i + 1), successor)
    )
    or
    last(this.getLastBodyChildTree(), predecessor, completion) and
    completion instanceof NormalCompletion and
    successor = this.getBackgroundStep().getCompletion()
  }
}

private class BackgroundRunTree extends BackgroundTree instanceof Run {
  BackgroundRunTree() { this instanceof BackgroundStep }

  override BackgroundStep getBackgroundStep() { result = this }

  override AstNode getBodyChild(int i) {
    result =
      rank[i](AstNode child, Location l |
        (
          child = this.getInScopeEnvVarExpr(_) or
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

private class BackgroundUsesTree extends BackgroundTree instanceof UsesStep {
  BackgroundUsesTree() { this instanceof BackgroundStep }

  override BackgroundStep getBackgroundStep() { result = this }

  override AstNode getBodyChild(int i) {
    result =
      rank[i](AstNode child, Location l |
        (
          child = this.(UsesStep).getArgumentExpr(_) or
          child = this.getInScopeEnvVarExpr(_)
        ) and
        l = child.getLocation()
      |
        child
        order by
          l.getStartLine(), l.getStartColumn(), l.getEndColumn(), l.getEndLine(), child.toString()
      )
  }
}

private class BackgroundCompletionLeaf extends LeafTree instanceof BackgroundCompletion {
  override predicate succ(AstNode predecessor, AstNode successor, Completion completion) { none() }
}

private class WaitTree extends LeafTree instanceof WaitStep {
  override predicate succ(AstNode predecessor, AstNode successor, Completion completion) {
    exists(BackgroundStep background |
      background = this.(WaitStep).getATargetStep() and
      predecessor = background.getCompletion() and
      successor = this and
      completion instanceof SimpleCompletion
    )
  }
}

private class WaitAllTree extends LeafTree instanceof WaitAllStep {
  override predicate succ(AstNode predecessor, AstNode successor, Completion completion) {
    exists(BackgroundStep background |
      background = this.(WaitAllStep).getATargetStep() and
      predecessor = background.getCompletion() and
      successor = this and
      completion instanceof SimpleCompletion
    )
  }
}

private class CancelTree extends LeafTree instanceof CancelStep {
  override predicate succ(AstNode predecessor, AstNode successor, Completion completion) { none() }
}

private class ParallelTree extends ControlFlowTree instanceof ParallelStep {
  private ControlFlowTree getChildTree(int i) { result = this.(ParallelStep).getStep(i) }

  override predicate first(AstNode firstNode) {
    first(this.getChildTree(_), firstNode)
    or
    not exists(this.getChildTree(_)) and firstNode = this
  }

  override predicate last(AstNode lastNode, Completion completion) {
    lastNode = this and completion instanceof SimpleCompletion
  }

  override predicate propagatesAbnormal(AstNode child) {
    child = this.(ParallelStep).getAStep()
  }

  override predicate succ(AstNode predecessor, AstNode successor, Completion completion) {
    last(this.getChildTree(_), predecessor, completion) and
    completion instanceof NormalCompletion and
    successor = this
  }
}

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

  override predicate last(AstNode lastNode, Completion completion) {
    super.last(lastNode, completion)
    or
    exists(BackgroundStep background |
      this.(LocalJob).getAContainedStep() = background and
      not exists(background.getBarrier()) and
      lastNode = background.getCompletion() and
      completion instanceof SimpleCompletion
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
  UsesTree() { not this instanceof BackgroundStep }

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
  RunTree() { not this instanceof BackgroundStep }

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
