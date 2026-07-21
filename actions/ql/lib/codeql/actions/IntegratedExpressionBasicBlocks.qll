/** Provides basic blocks over the integrated Actions and expression control-flow graph. */

import codeql.actions.IntegratedExpressionControlFlow as IntegratedCfg
private import codeql.actions.Cfg as ActionsCfg
private import codeql.Locations
private import codeql.controlflow.BasicBlock as SharedBasicBlock
private import codeql.controlflow.SuccessorType

private module Input implements SharedBasicBlock::InputSig<Location> {
  class CfgScope = ActionsCfg::CfgScope;

  class Node = IntegratedCfg::Node;

  CfgScope nodeGetCfgScope(Node node) { result = node.getScope() }

  Node nodeGetASuccessor(Node node, SuccessorType type) {
    result = node.getASuccessorWithType(type)
  }

  predicate nodeIsDominanceEntry(Node node) {
    node instanceof IntegratedCfg::ActionsNode and
    node.(IntegratedCfg::ActionsNode).getCfgNode() instanceof ActionsCfg::EntryNode
  }

  predicate nodeIsPostDominanceExit(Node node) {
    node instanceof IntegratedCfg::ActionsNode and
    node.(IntegratedCfg::ActionsNode).getCfgNode() instanceof ActionsCfg::NormalExitNode
  }
}

module Cfg = SharedBasicBlock::Make<Location, Input>;

class BasicBlock = Cfg::BasicBlock;

class EntryBasicBlock = Cfg::EntryBasicBlock;

/** A basic block ending in an operand-level Boolean branch. */
class ConditionBlock extends BasicBlock {
  ConditionBlock() { exists(this.getLastNode().getASuccessorWithType(any(BooleanSuccessor type))) }
}
