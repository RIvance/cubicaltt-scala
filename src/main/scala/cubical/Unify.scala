package cubical

import Val.*
import Eval.{nominalVal, nominalEnvironment}

/**
 * Pattern unification for metavariable solving during elaboration.
 *
 * `unify` is the meta-aware analogue of `Eval.convert`: it checks whether
 * two values are definitionally equal, but when one side is an unsolved
 * metavariable `VMeta(id)` it *solves* the meta by recording the other
 * side as its solution.  When both sides are rigid and unequal, it throws
 * `TypeCheckError` (same as what `TypeChecker` throws when `convert` fails).
 *
 * The `MetaContext` is threaded immutably through every recursive call and
 * returned alongside the (possibly updated) context after each equation.
 *
 * Design note: `Eval.convert` remains unchanged — it is still used by
 * `TypeChecker` which never sees unsolved metas (the Elaborator zonks
 * all terms before handing them to the core checker).  `unify` is used
 * exclusively by the Elaborator during the elaboration phase.
 */
object Unify {

  /**
   * Unify two values, solving metas as needed.
   *
   * @param ns      names in scope (for fresh variable generation)
   * @param u       left-hand value
   * @param v       right-hand value
   * @param metaCtx current metavariable context
   * @return updated MetaContext (with any newly solved metas)
   * @throws TypeCheckError if the values are not definitionally equal
   */
  def unify(ns: List[String], u: Val, v: Val, metaCtx: MetaContext): MetaContext = {
    val fu = MetaContext.force(metaCtx, u)
    val fv = MetaContext.force(metaCtx, v)
    if (fu == fv) return metaCtx

    (fu, fv) match {
      // Flex-rigid / flex-flex: solve the meta
      case (VMeta(id), rhs) =>
        metaCtx.solve(id, rhs)
      case (lhs, VMeta(id)) =>
        metaCtx.solve(id, lhs)

      // Closures: η-expand and recurse
      case (Closure(Term.Lam(_, x, a, u1), e), Closure(Term.Lam(_, x2, _, u2), e2)) =>
        val w @ VVar(n, _) = Eval.mkVarNice(ns, x, Eval.eval(a, e)): @unchecked
        unify(n :: ns, Eval.eval(u1, Environment.update((x, w), e)), Eval.eval(u2, Environment.update((x2, w), e2)), metaCtx)
      case (Closure(Term.Lam(_, x, a, u1), e), u2) =>
        val w @ VVar(n, _) = Eval.mkVarNice(ns, x, Eval.eval(a, e)): @unchecked
        unify(n :: ns, Eval.eval(u1, Environment.update((x, w), e)), Eval.app(u2, w), metaCtx)
      case (u1, Closure(Term.Lam(_, x, a, u2), e)) =>
        val w @ VVar(n, _) = Eval.mkVarNice(ns, x, Eval.eval(a, e)): @unchecked
        unify(n :: ns, Eval.app(u1, w), Eval.eval(u2, Environment.update((x, w), e)), metaCtx)

      // Closure identity checks (split, sum, undef, hole)
      case (Closure(Term.Split(_, p, _, _), e), Closure(Term.Split(_, p2, _, _), e2)) =>
        if (p != p2) fail(fu, fv)
        unifyEnv(ns, e, e2, metaCtx)
      case (Closure(Term.Sum(p, _, _), e), Closure(Term.Sum(p2, _, _), e2)) =>
        if (p != p2) fail(fu, fv)
        unifyEnv(ns, e, e2, metaCtx)
      case (Closure(Term.HSum(p, _, _), e), Closure(Term.HSum(p2, _, _), e2)) =>
        if (p != p2) fail(fu, fv)
        unifyEnv(ns, e, e2, metaCtx)
      case (Closure(Term.Undef(p, _), e), Closure(Term.Undef(p2, _), e2)) =>
        if (p != p2) fail(fu, fv)
        unifyEnv(ns, e, e2, metaCtx)
      case (Closure(Term.Hole(p), e), Closure(Term.Hole(p2), e2)) =>
        if (p != p2) fail(fu, fv)
        unifyEnv(ns, e, e2, metaCtx)

      // Π and Σ
      case (VPi(_, u1, v1), VPi(_, u2, v2)) =>
        val w @ VVar(n, _) = Eval.mkVarNice(ns, "X", u1): @unchecked
        val mc1 = unify(ns, u1, u2, metaCtx)
        unify(n :: ns, Eval.app(v1, w), Eval.app(v2, w), mc1)
      case (VSigma(u1, v1), VSigma(u2, v2)) =>
        val w @ VVar(n, _) = Eval.mkVarNice(ns, "X", u1): @unchecked
        val mc1 = unify(ns, u1, u2, metaCtx)
        unify(n :: ns, Eval.app(v1, w), Eval.app(v2, w), mc1)

      // Constructors
      case (VCon(c, us1), VCon(c2, us2)) =>
        if (c != c2) fail(fu, fv)
        unifyList(ns, us1, us2, metaCtx)
      case (VPCon(c, v1, us1, phis1), VPCon(c2, v2, us2, phis2)) =>
        if (c != c2) fail(fu, fv)
        if (!Eval.convertFormulas(ns, phis1, phis2)) fail(fu, fv)
        val mc1 = unify(ns, v1, v2, metaCtx)
        unifyList(ns, us1, us2, mc1)

      // Pairs (with η)
      case (VPair(u1, v1), VPair(u2, v2)) =>
        val mc1 = unify(ns, u1, u2, metaCtx)
        unify(ns, v1, v2, mc1)
      case (VPair(u1, v1), w) =>
        val mc1 = unify(ns, u1, Eval.fstVal(w), metaCtx)
        unify(ns, v1, Eval.sndVal(w), mc1)
      case (w, VPair(u2, v2)) =>
        val mc1 = unify(ns, Eval.fstVal(w), u2, metaCtx)
        unify(ns, Eval.sndVal(w), v2, mc1)

      // Neutral eliminators
      case (VFst(u1), VFst(u2)) => unify(ns, u1, u2, metaCtx)
      case (VSnd(u1), VSnd(u2)) => unify(ns, u1, u2, metaCtx)
      case (VApp(u1, v1), VApp(u2, v2)) =>
        val mc1 = unify(ns, u1, u2, metaCtx)
        unify(ns, v1, v2, mc1)
      case (VSplit(u1, v1), VSplit(u2, v2)) =>
        val mc1 = unify(ns, u1, u2, metaCtx)
        unify(ns, v1, v2, mc1)

      // Atomic neutrals
      case (VOpaque(x, _), VOpaque(x2, _)) =>
        if (x != x2) fail(fu, fv)
        metaCtx
      case (VVar(x, _), VVar(x2, _)) =>
        if (x != x2) fail(fu, fv)
        metaCtx

      // Path types
      case (VPathP(a, b, c), VPathP(a2, b2, c2)) =>
        val mc1 = unify(ns, a, a2, metaCtx)
        val mc2 = unify(ns, b, b2, mc1)
        unify(ns, c, c2, mc2)

      // Path lambdas (with η)
      case (VPLam(i, a), VPLam(i2, a2)) =>
        val j = Nominal.fresh((fu, fv))
        unify(ns, Nominal.swap(a, (i, j)), Nominal.swap(a2, (i2, j)), metaCtx)
      case (VPLam(i, a), p2) =>
        val j = Nominal.fresh((fu, fv))
        unify(ns, Nominal.swap(a, (i, j)), Eval.appFormula(p2, Formula.Atom(j)), metaCtx)
      case (p, VPLam(i2, a2)) =>
        val j = Nominal.fresh((fu, fv))
        unify(ns, Eval.appFormula(p, Formula.Atom(j)), Nominal.swap(a2, (i2, j)), metaCtx)

      // Path application
      case (VAppFormula(u1, x), VAppFormula(u2, x2)) =>
        if (!Eval.convertFormula(ns, x, x2)) fail(fu, fv)
        unify(ns, u1, u2, metaCtx)

      // Composition
      case (VComp(a, u1, ts), VComp(a2, u2, ts2)) =>
        val mc1 = unify(ns, a, a2, metaCtx)
        val mc2 = unify(ns, u1, u2, mc1)
        unifySystem(ns, ts, ts2, mc2)
      case (VHComp(a, u1, ts), VHComp(a2, u2, ts2)) =>
        val mc1 = unify(ns, a, a2, metaCtx)
        val mc2 = unify(ns, u1, u2, mc1)
        unifySystem(ns, ts, ts2, mc2)

      // Glue types
      case (VGlue(v1, equivs1), VGlue(v2, equivs2)) =>
        val mc1 = unify(ns, v1, v2, metaCtx)
        unifySystem(ns, equivs1, equivs2, mc1)

      // Glue elements (with unglue η)
      case (VGlueElem(VUnGlueElem(b, equivs), ts), g) =>
        if (!Eval.convertSystem(ns, Nominal.border(b, equivs), ts)) fail(fu, fv)
        unify(ns, b, g, metaCtx)
      case (g, VGlueElem(VUnGlueElem(b, equivs), ts)) =>
        if (!Eval.convertSystem(ns, Nominal.border(b, equivs), ts)) fail(fu, fv)
        unify(ns, b, g, metaCtx)
      case (VGlueElem(VUnGlueElemU(b, _, equivs), ts), g) =>
        if (!Eval.convertSystem(ns, Nominal.border(b, equivs), ts)) fail(fu, fv)
        unify(ns, b, g, metaCtx)
      case (g, VGlueElem(VUnGlueElemU(b, _, equivs), ts)) =>
        if (!Eval.convertSystem(ns, Nominal.border(b, equivs), ts)) fail(fu, fv)
        unify(ns, b, g, metaCtx)
      case (VGlueElem(u1, us1), VGlueElem(u2, us2)) =>
        val mc1 = unify(ns, u1, u2, metaCtx)
        unifySystem(ns, us1, us2, mc1)

      // UnGlueElem
      case (VUnGlueElemU(u1, _, _), VUnGlueElemU(u2, _, _)) => unify(ns, u1, u2, metaCtx)
      case (VUnGlueElem(u1, _), VUnGlueElem(u2, _)) => unify(ns, u1, u2, metaCtx)

      // CompU
      case (VCompU(u1, es1), VCompU(u2, es2)) =>
        val mc1 = unify(ns, u1, u2, metaCtx)
        unifySystem(ns, es1, es2, mc1)

      // Identity types
      case (VIdPair(v1, vs1), VIdPair(v2, vs2)) =>
        val mc1 = unify(ns, v1, v2, metaCtx)
        unifySystem(ns, vs1, vs2, mc1)
      case (VId(a, u1, v1), VId(a2, u2, v2)) =>
        val mc1 = unify(ns, a, a2, metaCtx)
        val mc2 = unify(ns, u1, u2, mc1)
        unify(ns, v1, v2, mc2)
      case (VIdJ(a, u1, c, d, x, p), VIdJ(a2, u2, c2, d2, x2, p2)) =>
        unifyList(ns, List(a, u1, c, d, x, p), List(a2, u2, c2, d2, x2, p2), metaCtx)

      case _ => fail(fu, fv)
    }
  }

  private def unifyList(ns: List[String], us: List[Val], vs: List[Val], metaCtx: MetaContext): MetaContext = {
    if (us.length != vs.length) throw TypeCheckError(s"unify: list length mismatch")
    us.zip(vs).foldLeft(metaCtx) { case (mc, (u, v)) => unify(ns, u, v, mc) }
  }

  private def unifySystem(ns: List[String], ts: System[Val], ts2: System[Val], metaCtx: MetaContext): MetaContext = {
    if (ts.keys.toSet != ts2.keys.toSet)
      throw TypeCheckError(s"unify: system key mismatch")
    ts.foldLeft(metaCtx) { case (mc, (k, v)) =>
      unify(ns, v, ts2(k), mc)
    }
  }

  private def unifyEnv(ns: List[String], e1: Environment, e2: Environment, metaCtx: MetaContext): MetaContext = {
    if (!Eval.convertContext(ns, e1.ctx, e2.ctx))
      throw TypeCheckError(s"unify: environment context mismatch")
    val mc1 = unifyList(ns, e1.vals, e2.vals, metaCtx)
    if (!Eval.convertFormulas(ns, e1.formulas, e2.formulas))
      throw TypeCheckError(s"unify: environment formula mismatch")
    mc1
  }

  private def fail(u: Val, v: Val): Nothing =
    throw TypeCheckError(s"unify:\n$u\n/=\n$v")
}
