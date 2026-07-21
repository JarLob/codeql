import codeql.actions.Ast
import codeql.actions.Cfg as Cfg
import codeql.actions.controlflow.BasicBlocks
import codeql.controlflow.SuccessorType

query predicate conditionEdges(If condition, AstNode successor, string branch) {
  exists(Cfg::Node conditionNode, Cfg::Node successorNode, BooleanSuccessor edge |
    conditionNode.getAstNode() = condition and
    successorNode = conditionNode.getASuccessor(edge) and
    successor = successorNode.getAstNode() and
    branch = edge.getValue().toString()
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
