package cubical

/**
 * Metavariable infrastructure for bidirectional elaboration.
 *
 * A metavariable (written `?n` in debug output) represents an unknown value
 * to be determined by unification during type checking.  Each meta carries
 * the type it must inhabit; its `solution` starts as `None` and becomes
 * `Some(v)` once unification finds a unique answer.
 *
 * `MetaContext` is an **immutable** value threaded through every elaboration
 * call, following the same pure-functional style as `TypeEnv` and
 * `Environment` in the rest of the core.
 *
 * Key operations:
 *   - `freshMeta`  — allocate a new unsolved meta of a given type
 *   - `solve`      — record a solution for a meta (idempotent if consistent)
 *   - `lookupMeta` — retrieve the entry for a meta id
 *   - `force`      — follow solved-meta chains to a head-normal value
 *   - `zonkTerm`   — substitute all solved metas in a `Term`
 *   - `zonkVal`    — substitute all solved metas in a `Val`
 */

case class MetaEntry(ty: Val, solution: Option[Val])

/**
 * Immutable context tracking all metavariables created during elaboration
 * of a single top-level declaration.
 *
 * @param metas  map from meta id to its entry (type + optional solution)
 * @param nextId the id that will be assigned to the next fresh meta
 */
case class MetaContext(
  metas: Map[Int, MetaEntry],
  nextId: Int
) {

  /** Allocate a fresh unsolved metavariable of the given type. */
  def freshMeta(ty: Val): (Val, MetaContext) = {
    val id = nextId
    val entry = MetaEntry(ty, solution = None)
    val updated = MetaContext(metas.updated(id, entry), nextId + 1)
    (Val.VMeta(id), updated)
  }

  /** Record `value` as the solution for meta `id`. */
  def solve(id: Int, value: Val): MetaContext = {
    val entry = metas.getOrElse(id, throw ElaborationError(s"solve: unknown meta ?$id"))
    entry.solution match {
      case Some(_) =>
        throw ElaborationError(s"solve: meta ?$id already solved")
      case None =>
        MetaContext(metas.updated(id, entry.copy(solution = Some(value))), nextId)
    }
  }

  /** Look up the entry for a meta id. */
  def lookupMeta(id: Int): MetaEntry =
    metas.getOrElse(id, throw ElaborationError(s"lookupMeta: unknown meta ?$id"))

  /** True when every allocated meta has been solved. */
  def allSolved: Boolean = metas.values.forall(_.solution.isDefined)

  /** Return the ids of all unsolved metas. */
  def unsolvedMetas: List[Int] = metas.collect { case (id, MetaEntry(_, None)) => id }.toList.sorted
}

object MetaContext {
  val empty: MetaContext = MetaContext(Map.empty, nextId = 0)

  /**
   * Follow solved-meta indirections to reach a head value.
   *
   * If `value` is `VMeta(id)` and `id` is solved, recursively force the
   * solution.  Otherwise return `value` unchanged.  This is the analogue
   * of "read-back through the meta store" — callers should force before
   * pattern-matching on a `Val` whenever metas may be present.
   */
  def force(metaCtx: MetaContext, value: Val): Val = value match {
    case Val.VMeta(id) =>
      metaCtx.metas.get(id) match {
        case Some(MetaEntry(_, Some(solution))) => force(metaCtx, solution)
        case _                                  => value
      }
    case _ => value
  }

  /**
   * Zonk a `Term`: replace every `Meta(id)` whose solution is known with
   * the normal form of that solution, recursively.
   *
   * This produces a fully elaborated term suitable for evaluation by the
   * existing `Eval.eval`, which does not know about metas.
   */
  def zonkTerm(metaCtx: MetaContext, term: Term): Term = term match {
    case Term.Meta(id) =>
      metaCtx.metas.get(id) match {
        case Some(MetaEntry(_, Some(solution))) =>
          zonkTerm(metaCtx, readBackVal(metaCtx, solution))
        case Some(MetaEntry(_, None)) =>
          throw ElaborationError(s"zonkTerm: unsolved meta ?$id")
        case None =>
          throw ElaborationError(s"zonkTerm: unknown meta ?$id")
      }
    case Term.U => Term.U
    case Term.Var(name) => Term.Var(name)
    case Term.App(icity, fun, arg) =>
      Term.App(icity, zonkTerm(metaCtx, fun), zonkTerm(metaCtx, arg))
    case Term.Pi(icity, body) =>
      Term.Pi(icity, zonkTerm(metaCtx, body))
    case Term.Lam(icity, name, ty, body) =>
      Term.Lam(icity, name, zonkTerm(metaCtx, ty), zonkTerm(metaCtx, body))
    case Term.Where(body, decls) =>
      Term.Where(zonkTerm(metaCtx, body), zonkDecls(metaCtx, decls))
    case Term.Sigma(body) =>
      Term.Sigma(zonkTerm(metaCtx, body))
    case Term.Pair(fst, snd) =>
      Term.Pair(zonkTerm(metaCtx, fst), zonkTerm(metaCtx, snd))
    case Term.Fst(pair) => Term.Fst(zonkTerm(metaCtx, pair))
    case Term.Snd(pair) => Term.Snd(zonkTerm(metaCtx, pair))
    case Term.Con(name, args) =>
      Term.Con(name, args.map(zonkTerm(metaCtx, _)))
    case Term.PCon(name, dataType, args, phis) =>
      Term.PCon(name, zonkTerm(metaCtx, dataType), args.map(zonkTerm(metaCtx, _)), phis)
    case Term.Split(name, loc, ty, branches) =>
      Term.Split(name, loc, zonkTerm(metaCtx, ty), branches.map(zonkBranch(metaCtx, _)))
    case Term.Sum(loc, name, labels) =>
      Term.Sum(loc, name, labels.map(zonkLabel(metaCtx, _)))
    case Term.HSum(loc, name, labels) =>
      Term.HSum(loc, name, labels.map(zonkLabel(metaCtx, _)))
    case Term.Undef(loc, ty) =>
      Term.Undef(loc, zonkTerm(metaCtx, ty))
    case Term.Hole(loc) => Term.Hole(loc)
    case Term.PathP(pathTy, left, right) =>
      Term.PathP(zonkTerm(metaCtx, pathTy), zonkTerm(metaCtx, left), zonkTerm(metaCtx, right))
    case Term.PLam(dim, body) =>
      Term.PLam(dim, zonkTerm(metaCtx, body))
    case Term.AppFormula(path, phi) =>
      Term.AppFormula(zonkTerm(metaCtx, path), phi)
    case Term.Comp(ty, base, sys) =>
      Term.Comp(zonkTerm(metaCtx, ty), zonkTerm(metaCtx, base), zonkSystem(metaCtx, sys))
    case Term.Fill(ty, base, sys) =>
      Term.Fill(zonkTerm(metaCtx, ty), zonkTerm(metaCtx, base), zonkSystem(metaCtx, sys))
    case Term.HComp(ty, base, sys) =>
      Term.HComp(zonkTerm(metaCtx, ty), zonkTerm(metaCtx, base), zonkSystem(metaCtx, sys))
    case Term.Glue(base, sys) =>
      Term.Glue(zonkTerm(metaCtx, base), zonkSystem(metaCtx, sys))
    case Term.GlueElem(base, sys) =>
      Term.GlueElem(zonkTerm(metaCtx, base), zonkSystem(metaCtx, sys))
    case Term.UnGlueElem(base, sys) =>
      Term.UnGlueElem(zonkTerm(metaCtx, base), zonkSystem(metaCtx, sys))
    case Term.Id(ty, left, right) =>
      Term.Id(zonkTerm(metaCtx, ty), zonkTerm(metaCtx, left), zonkTerm(metaCtx, right))
    case Term.IdPair(witness, sys) =>
      Term.IdPair(zonkTerm(metaCtx, witness), zonkSystem(metaCtx, sys))
    case Term.IdJ(ty, left, mot, refl, right, path) =>
      Term.IdJ(
        zonkTerm(metaCtx, ty), zonkTerm(metaCtx, left), zonkTerm(metaCtx, mot),
        zonkTerm(metaCtx, refl), zonkTerm(metaCtx, right), zonkTerm(metaCtx, path))
  }

  private def zonkSystem(metaCtx: MetaContext, sys: System[Term]): System[Term] =
    sys.map { case (face, term) => (face, zonkTerm(metaCtx, term)) }

  private def zonkBranch(metaCtx: MetaContext, branch: Branch): Branch = branch match {
    case Branch.OrdinaryBranch(ctor, vars, body) =>
      Branch.OrdinaryBranch(ctor, vars, zonkTerm(metaCtx, body))
    case Branch.PathBranch(ctor, vars, dims, body) =>
      Branch.PathBranch(ctor, vars, dims, zonkTerm(metaCtx, body))
  }

  private def zonkLabel(metaCtx: MetaContext, label: Label): Label = label match {
    case Label.OrdinaryLabel(name, tele) =>
      Label.OrdinaryLabel(name, zonkTelescope(metaCtx, tele))
    case Label.PathLabel(name, tele, dims, sys) =>
      Label.PathLabel(name, zonkTelescope(metaCtx, tele), dims, zonkSystem(metaCtx, sys))
  }

  private def zonkTelescope(metaCtx: MetaContext, tele: Telescope): Telescope =
    tele.map { case (name, ty) => (name, zonkTerm(metaCtx, ty)) }

  private def zonkDecls(metaCtx: MetaContext, decls: Declarations): Declarations = decls match {
    case Declarations.MutualDecls(loc, declPairs) =>
      Declarations.MutualDecls(loc, declPairs.map { case (name, (ty, body)) =>
        (name, (zonkTerm(metaCtx, ty), zonkTerm(metaCtx, body)))
      })
    case other => other
  }

  /**
   * Read back (quote) a `Val` into a `Term`.
   *
   * This is a simplified quotation used by zonking: it only handles the
   * cases that can appear as meta solutions.  A full quotation would need
   * the name context for η-expansion; for now we piggyback on the fact
   * that meta solutions are typically small closed values.
   */
  def readBackVal(metaCtx: MetaContext, value: Val): Term = value match {
    case Val.VU => Term.U
    case Val.VMeta(id) => Term.Meta(id)
    case Val.VVar(name, _) => Term.Var(name)
    case Val.VApp(fun, arg) =>
      Term.App(Icity.Explicit, readBackVal(metaCtx, fun), readBackVal(metaCtx, arg))
    case Val.VPi(icity, domain, codomain) =>
      val x = "_"
      Term.Pi(icity, Term.Lam(icity, x, readBackVal(metaCtx, domain), readBackClosure(metaCtx, x, domain, codomain)))
    case Val.VSigma(fstTy, sndTy) =>
      val x = "_"
      Term.Sigma(Term.Lam(Icity.Explicit, x, readBackVal(metaCtx, fstTy), readBackClosure(metaCtx, x, fstTy, sndTy)))
    case Val.VPair(fst, snd) =>
      Term.Pair(readBackVal(metaCtx, fst), readBackVal(metaCtx, snd))
    case Val.VCon(name, args) =>
      Term.Con(name, args.map(readBackVal(metaCtx, _)))
    case Val.VPathP(pathTy, left, right) =>
      Term.PathP(readBackVal(metaCtx, pathTy), readBackVal(metaCtx, left), readBackVal(metaCtx, right))
    case Val.VPLam(dim, body) =>
      Term.PLam(dim, readBackVal(metaCtx, body))
    case Val.VLam(name, domain, body) =>
      Term.Lam(Icity.Explicit, name, readBackVal(metaCtx, domain), readBackVal(metaCtx, body))
    // Data type closures carry the name of the type they define.
    // Quoting them as `Var(name)` is sound because the name is always
    // in scope when the zonked term is re-evaluated by the core checker,
    // and `eval(Var(name), env)` will produce the identical closure.
    // Stripping the environment (the old approach) loses binding context
    // and causes spurious conversion failures.
    case Val.Closure(Term.Sum(_, name, _), _) => Term.Var(name)
    case Val.Closure(Term.HSum(_, name, _), _) => Term.Var(name)
    case Val.Closure(term, _) => zonkTerm(metaCtx, term)
    case other =>
      throw ElaborationError(s"readBackVal: cannot quote value: $other")
  }

  /**
   * Read back a closure body by applying it to a fresh variable and quoting the result.
   */
  private def readBackClosure(metaCtx: MetaContext, name: Ident, domain: Val, closure: Val): Term = {
    val freshVar = Val.VVar(name, domain)
    readBackVal(metaCtx, Eval.app(closure, freshVar))
  }
}

case class ElaborationError(msg: String) extends RuntimeException(msg)
