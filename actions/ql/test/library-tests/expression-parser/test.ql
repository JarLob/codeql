import codeql.actions.Ast

from If guard, ExpressionNode node, int line, int start, int end, string kind, string parentKind
where
  node.getExpression() = guard.getConditionExpr() and
  line = guard.getLocation().getStartLine() and
  start = node.getStartOffset() and
  end = node.getEndOffset() and
  kind = node.getKind() and
  (
    parentKind = node.getParent().getKind()
    or
    not exists(node.getParent()) and parentKind = "<none>"
  )
select guard, line, kind, parentKind, node.getText(), start, end order by line, start, end, kind

query predicate nodeLocations(
  ExpressionNode node, string text, int startLine, int startColumn, int endLine, int endColumn
) {
  node.getExpression().getRawExpression() =
    [
      "${{ github.actor }}", "${{ github.repository }}", "${{ github.ref }}",
      "fromJSON(inputs.matrix)[0].enabled != null"
    ] and
  text = node.getText() and
  startLine = node.getSourceStartLine() and
  startColumn = node.getSourceStartColumn() and
  endLine = node.getSourceEndLine() and
  endColumn = node.getSourceEndColumn()
}

query predicate rootLocationPrecision(string text, string precision) {
  exists(ExpressionRoot root |
    root.getExpression().getRawExpression() =
      ["${{ github.actor }}", "${{ github.repository }}", "${{ github.ref }}"] and
    text = root.getText() and
    (
      root.hasExactSourceLocation() and precision = "exact"
      or
      not root.hasExactSourceLocation() and precision = "containing scalar"
    )
  )
}

query predicate matrixExpressions(string kind, string expression, string target) {
  exists(MatrixAccessExpression access |
    kind = "access" and
    expression = access.getExpression().getExpression() and
    target = access.getTarget().toString()
  )
  or
  exists(MatrixContextExpression reference |
    kind = "context" and
    expression = reference.getExpression().getExpression() and
    target = reference.getATarget().toString()
  )
}
