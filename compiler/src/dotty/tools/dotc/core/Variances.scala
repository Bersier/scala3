package dotty.tools.dotc
package core

import Types.*, Contexts.*, Flags.*, Symbols.*, Annotations.*
import TypeApplications.TypeParamInfo
import Decorators.*

object Variances {

  object Vs:
    opaque type Variance = Int

    val invariant = 0
    val covariant = 1
    val contravariant = 2
    val bivariant = 3

    def fromFlagSet(flagSet: VarianceFlagSet): Variance =
      if flagSet.is(CovariantFlagSet) then
        if flagSet.is(ContravariantFlagSet)
        then bivariant
        else covariant
      else if flagSet.is(ContravariantFlagSet)
        then contravariant
        else invariant

    private final val flipLookupTable = 0xD8
    private final val timesLookupTable = 0xFFD8E4C0

    extension (v: Variance)
      inline def invert: Variance = v ^ 3
      inline def flip: Variance = (flipLookupTable >>> (v << 1)) & 3
      inline def *(w: Variance): Variance =
        (timesLookupTable >>> ((v << 3) | (w << 1))) & 3
      def toFlagSet: VarianceFlagSet = v match
        case 0 => InvariantFlagSet
        case 1 => CovariantFlagSet
        case 2 => ContravariantFlagSet
        case 3 => BivariantFlagSet
        case _ => throw AssertionError(s"Impossible variance: $v")
  end Vs

  type VarianceFlagSet = FlagSet
  val BivariantFlagSet: VarianceFlagSet = VarianceFlags
  val InvariantFlagSet: VarianceFlagSet = EmptyFlags

  def varianceFromInt(v: Int): VarianceFlagSet =
    if v < 0 then ContravariantFlagSet
    else if v > 0 then CovariantFlagSet
    else InvariantFlagSet

  def varianceToInt(v: VarianceFlagSet): Int =
    if v.is(CovariantFlagSet) then 1
    else if v.is(ContravariantFlagSet) then -1
    else 0

  /** Flip between covariant and contravariant */
  def flip(v: VarianceFlagSet): VarianceFlagSet =
    if (v == CovariantFlagSet) ContravariantFlagSet
    else if (v == ContravariantFlagSet) CovariantFlagSet
    else v

  def setStructuralVariances(lam: HKTypeLambda)(using Context): Unit =
    assert(!lam.isDeclaredVarianceLambda)
    for param <- lam.typeParams do param.storedVariance = BivariantFlagSet
    object narrowVariances extends TypeTraverser {
      def traverse(t: Type): Unit = t match
        case t: TypeParamRef if t.binder eq lam =>
          lam.typeParams(t.paramNum).storedVariance &= varianceFromInt(variance)
        case _ =>
          traverseChildren(t)
    }
    // Note: Normally, we'd need to repeat `traverse` until a fixpoint is reached.
    // But since recursive lambdas can only appear in bounds, and bounds never have
    // structural variances, a single traversal is enough.
    narrowVariances.traverse(lam.resType)

  /** Does variance `v1` conform to variance `v2`?
   *  This is the case if the variances are the same or `sym` is nonvariant.
   */
  def varianceConforms(v1: Int, v2: Int): Boolean =
    v1 == v2 || v2 == 0

  /** Does the variance of type parameter `tparam1` conform to the variance of type parameter `tparam2`?
   */
  def varianceConforms(tparam1: TypeParamInfo, tparam2: TypeParamInfo)(using Context): Boolean =
    tparam1.paramVariance.isAllOf(tparam2.paramVariance)

  /** Do the variances of type parameters `tparams1` conform to the variances
   *  of corresponding type parameters `tparams2`?
   *  This is only the case if `tparams1` and `tparams2` have the same length.
   */
  def variancesConform(tparams1: List[TypeParamInfo], tparams2: List[TypeParamInfo])(using Context): Boolean =
    val needsDetailedCheck = tparams2 match
      case (_: Symbol) :: _ => true
      case LambdaParam(tl: HKTypeLambda, _) :: _ => tl.isDeclaredVarianceLambda
      case _ => false
    if needsDetailedCheck then tparams1.corresponds(tparams2)(varianceConforms)
    else tparams1.hasSameLengthAs(tparams2)

  def varianceSign(v: VarianceFlagSet): String = varianceSign(varianceToInt(v))
  def varianceLabel(v: VarianceFlagSet): String = varianceLabel(varianceToInt(v))

  def varianceSign(v: Int): String =
    if (v > 0) "+"
    else if (v < 0) "-"
    else ""

  def varianceLabel(v: Int): String =
    if v < 0 then "contravariant"
    else if v > 0 then "covariant"
    else "invariant"

  val alwaysInvariant: Any => InvariantFlagSet.type = Function.const(InvariantFlagSet)
}
