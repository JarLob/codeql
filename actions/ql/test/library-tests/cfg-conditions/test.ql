import codeql.actions.Ast
import codeql.actions.Cfg as Cfg
import codeql.actions.controlflow.BasicBlocks
import codeql.actions.IntegratedExpressionControlFlow as IntegratedCfg
import codeql.actions.IntegratedExpressionBasicBlocks as IntegratedBlocks
import codeql.controlflow.SuccessorType

query predicate conditionEdges(If condition, AstNode successor, string branch) {
  exists(Cfg::Node conditionNode, Cfg::Node successorNode, BooleanSuccessor edge |
    conditionNode.getAstNode() = condition and
    successorNode = conditionNode.getASuccessor(edge) and
    successor = successorNode.getAstNode() and
    branch = edge.getValue().toString()
  )
}

query predicate integratedBasicBlockBranches(string expression, boolean branch, string successor) {
  exists(
    IntegratedBlocks::ConditionBlock block, IntegratedBlocks::BasicBlock successorBlock,
    BooleanSuccessor edge
  |
    successorBlock = block.getASuccessor(edge) and
    expression = block.getLastNode().toString() and
    branch = edge.getValue() and
    successor = successorBlock.getFirstNode().toString()
  )
}

query predicate integratedBasicBlockBranchDominance(
  string expression, boolean branch, AstNode controlled
) {
  exists(
    IntegratedBlocks::ConditionBlock block, IntegratedBlocks::BasicBlock branchBlock,
    IntegratedBlocks::BasicBlock controlledBlock, IntegratedCfg::ActionsNode controlledNode,
    BooleanSuccessor edge
  |
    branchBlock = block.getASuccessor(edge) and
    branchBlock.dominates(controlledBlock) and
    controlledNode = controlledBlock.getANode() and
    controlled = controlledNode.getCfgNode().getAstNode() and
    (controlled instanceof Job or controlled instanceof Run)
  |
    expression = block.getLastNode().toString() and branch = edge.getValue()
  )
}

query predicate controlledBlocks(If condition, AstNode controlled, string branch) {
  exists(ConditionBlock conditionBlock, BasicBlock controlledBlock, BooleanSuccessor edge |
    conditionBlock.getLastNode().getAstNode() = condition and
    conditionBlock.controls(controlledBlock, edge) and
    controlled = controlledBlock.getANode().getAstNode() and
    branch = edge.getValue().toString()
  )
}

query predicate integratedConditionEntries(If condition, ExpressionRoot root) {
  exists(IntegratedCfg::ActionsNode conditionNode, IntegratedCfg::ExpressionNode successor |
    conditionNode.getCfgNode().getAstNode() = condition and
    successor = conditionNode.getASuccessor() and
    successor.getExpressionCfgNode() =
      IntegratedCfg::ExpressionCfg::getEntryNode(condition.getConditionExpr()) and
    root = successor.getExpressionCfgNode().getExpressionNode()
  )
}

query predicate integratedConditionCompletions(If condition, boolean outcome, AstNode successor) {
  exists(
    IntegratedCfg::ExpressionNode completionNode, IntegratedCfg::ActionsNode successorNode,
    IntegratedCfg::ExpressionCfg::CompletionNode completion
  |
    completionNode.getExpressionCfgNode() = completion and
    completion.getExpressionNode() = condition.getConditionExpr().getRoot() and
    outcome = completion.getOutcome() and
    successorNode = completionNode.getASuccessor() and
    successor = successorNode.getCfgNode().getAstNode()
  )
}
