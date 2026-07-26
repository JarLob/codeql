private import actions
import codeql.actions.DataFlow
private import codeql.actions.dataflow.internal.ExternalFlowSinks as ExternalFlowSinks

private predicate isDirectWholeValueAccess(Expression expression) {
  expression.getParentNode().(ScalarValue).getValue().trim() = expression.getRawExpression().trim() and
  expression.getRoot().getChild(0) instanceof AccessExpression
}

class CodeInjectionSink extends DataFlow::Node {
  CodeInjectionSink() {
    exists(Run e | e.getAnScriptExpr() = this.asExpr())
    or
    exists(LocalJob job, Expression image |
      job.getJobContainerImageExpr() = image and
      this.asExpr() = image and
      isDirectWholeValueAccess(image)
    )
    or
    isModeledCodeInjectionSink(this)
  }
}

predicate isModeledCodeInjectionSink(DataFlow::Node sink) {
  ExternalFlowSinks::modeledSink(sink, "code-injection")
}