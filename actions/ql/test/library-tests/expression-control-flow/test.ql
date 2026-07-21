import codeql.actions.ExpressionControlFlow

query predicate shortCircuitEdges(string job, boolean leftOutcome, Node successor) {
  exists(BinaryExpression binary, CompletionNode leftCompletion |
    job = binary.getExpression().getEnclosingJob().getId() and
    job = ["partial-and", "partial-or"] and
    leftCompletion.getExpressionNode() = binary.getLeftOperand() and
    leftOutcome = leftCompletion.getOutcome() and
    successor = leftCompletion.getASuccessor()
  )
}

query predicate pullRequestRightOperandReachability(string job, EvaluationNode rightOperand) {
  exists(Event event, EvaluationNode entry, BinaryExpression binary |
    event = binary.getExpression().getEnclosingWorkflow().getOn().getAnEvent() and
    event.getName() = "pull_request" and
    job = binary.getExpression().getEnclosingJob().getId() and
    job = ["partial-and", "partial-or"] and
    entry = getEntryNode(binary.getExpression()) and
    rightOperand.getExpressionNode() = binary.getRightOperand() and
    rightOperand = entry.getAReachableNode(event)
  )
}

query predicate pullRequestFinalOutcomes(string job, boolean outcome) {
  exists(Event event, EvaluationNode entry, CompletionNode completion |
    event = completion.getExpression().getEnclosingWorkflow().getOn().getAnEvent() and
    event.getName() = "pull_request" and
    job = completion.getExpression().getEnclosingJob().getId() and
    entry = getEntryNode(completion.getExpression()) and
    completion = getACompletionNode(completion.getExpression()) and
    outcome = completion.getOutcome() and
    completion = entry.getAReachableNode(event)
  )
}
