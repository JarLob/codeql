// generated by codegen/codegen.py, do not edit
/**
 * This module provides the generated definition of `ExplicitClosureExpr`.
 * INTERNAL: Do not import directly.
 */

private import codeql.swift.generated.Synth
private import codeql.swift.generated.Raw
import codeql.swift.elements.expr.internal.ClosureExprImpl::Impl as ClosureExprImpl

/**
 * INTERNAL: This module contains the fully generated definition of `ExplicitClosureExpr` and should not
 * be referenced directly.
 */
module Generated {
  /**
   * INTERNAL: Do not reference the `Generated::ExplicitClosureExpr` class directly.
   * Use the subclass `ExplicitClosureExpr`, where the following predicates are available.
   */
  class ExplicitClosureExpr extends Synth::TExplicitClosureExpr, ClosureExprImpl::ClosureExpr {
    override string getAPrimaryQlClass() { result = "ExplicitClosureExpr" }
  }
}
