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

query predicate pushStepReachability(string source, string target) {
  exists(Step sourceStep, Step targetStep, Event event |
    sourceStep.getEnclosingJob().getId() = "guarded" and
    targetStep.getEnclosingJob() = sourceStep.getEnclosingJob() and
    source = sourceStep.getId() and
    source = "guarded-step" and
    target = targetStep.getId() and
    event = sourceStep.getEnclosingWorkflow().getOn().getAnEvent() and
    event.getName() = "push" and
    IntegratedCfg::mayReachForEvent(sourceStep, targetStep, event)
  )
}

query predicate pushStepCoExecution(string left, string right) {
  exists(Step leftStep, Step rightStep, Event event |
    leftStep.getEnclosingJob().getId() = "guarded" and
    rightStep.getEnclosingJob() = leftStep.getEnclosingJob() and
    left = leftStep.getId() and
    left = "guarded-step" and
    right = rightStep.getId() and
    event = leftStep.getEnclosingWorkflow().getOn().getAnEvent() and
    event.getName() = "push" and
    IntegratedCfg::mayCoExecuteForEvent(leftStep, rightStep, event)
  )
}

query predicate publicConditionDominance(If condition, AstNode controlled) {
  (
    controlled = condition.getEnclosingJob()
    or
    exists(Step step | step.getIf() = condition | controlled = step)
  ) and
  IntegratedBlocks::conditionTrueDominates(condition, controlled)
}

query predicate publicAstDominance(Step dominator, Step controlled) {
  dominator.getId() = "guarded-step" and
  controlled.getId() = "next-step" and
  IntegratedBlocks::astNodeDominates(dominator, controlled)
}
