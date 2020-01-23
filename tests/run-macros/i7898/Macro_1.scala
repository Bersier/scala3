import quoted._
import quoted.unsafe._
object Main {

  def myMacroImpl(body: Expr[_])(given qctx: QuoteContext): Expr[_] = {
    import qctx.tasty.{_, given}
    val bodyTerm = UnsafeExpr.underlyingArgument(body).unseal
    val showed = bodyTerm.show
    '{
      println(${Expr(showed)})
      ${bodyTerm.seal}
    }
  }

  inline def myMacro(body: => Any) <: Any = ${
    myMacroImpl('body)
  }
}
