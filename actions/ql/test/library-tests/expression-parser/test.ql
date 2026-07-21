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
