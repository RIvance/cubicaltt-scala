package cubical

/**
 * Thrown when name resolution encounters an unresolvable name, a scope error,
 * or any other structural problem in a `RawTerm` / `RawDecl` tree.
 *
 * Mirrors `TypeCheckError` and `EvalError` in the rest of the pipeline.
 */
case class ResolveError(msg: String) extends RuntimeException(msg)

/**
 * Symbol kind: distinguishes the different namespaces that a single `Ident`
 * can inhabit after declaration.
 *
 * Used by `ResolverEnv` to decide what `Term` node a raw `RawTerm.Var(x)`
 * should map to:
 *   - `Variable`     → `Term.Var(x)`
 *   - `Constructor`  → `Term.Con(x, args)`
 *   - `PConstructor` → `Term.PCon(x, …)` (path constructor, requires `{A}`)
 *   - `DimName`      → `Formula.Atom(Name(x))` (dimension variable, not a term)
 */
sealed trait SymKind
object SymKind {
  case object Variable     extends SymKind
  case object Constructor  extends SymKind
  case object PConstructor extends SymKind
  case object DimName      extends SymKind
}

/**
 * The name-resolution environment threaded through `Resolver`.
 *
 * `variables` is a LIFO stack of `(name, kind)` pairs; the most recently
 * bound name shadows earlier ones.  Lookup returns the innermost binding.
 */
case class ResolverEnv(
  moduleName: String,
  variables: List[(Ident, SymKind)]
) {
  def insertIdent(name: Ident, kind: SymKind): ResolverEnv =
    if (name == "_") this
    else copy(variables = (name, kind) :: variables)

  def insertIdents(pairs: List[(Ident, SymKind)]): ResolverEnv =
    pairs.foldLeft(this)((env, pair) => env.insertIdent(pair._1, pair._2))

  def insertVar(name: Ident): ResolverEnv  = insertIdent(name, SymKind.Variable)
  def insertVars(names: List[Ident]): ResolverEnv = names.foldLeft(this)(_.insertVar(_))

  def insertName(name: Ident): ResolverEnv = insertIdent(name, SymKind.DimName)
  def insertNames(names: List[Ident]): ResolverEnv = names.foldLeft(this)(_.insertName(_))

  def lookupKind(name: Ident): Option[SymKind] =
    variables.find(_._1 == name).map(_._2)
}

object ResolverEnv {
  val empty: ResolverEnv = ResolverEnv("", Nil)
}

/**
 * The result of resolving a `.ctt` module: resolved `Declarations`, and the
 * flat list of top-level names with their `SymKind` (used by importers).
 */
case class ParsedModule(
  name: String,
  imports: List[String],
  declarations: List[Declarations],
  names: List[(Ident, SymKind)]
)

/**
 * Just the module name and import list, extracted without full resolution.
 * Used by the import loader to determine the dependency order before full
 * resolution.
 */
case class ParsedImports(name: String, imports: List[String])

/**
 * Name resolver: transforms `RawTerm → Term` by resolving every `RawTerm.Var`
 * and `RawFormula.Atom` to the correct `Term`/`Formula` node according to
 * `ResolverEnv`.
 *
 * The resolver is stateful (it tracks a mutable `ResolverEnv` that grows as
 * declarations are processed in order) but is not re-entrant.  Create a fresh
 * `Resolver` instance per module.
 *
 * All methods throw `ResolveError` on failure instead of returning `Either`.
 */
class Resolver(moduleName: String, existingNames: List[(Ident, SymKind)]) {

  private var env: ResolverEnv = ResolverEnv(moduleName, existingNames)
  private var locCounter: Int  = 0

  private def freshLoc(): Loc = { locCounter += 1; Loc("", locCounter, 0) }

  /**
   * Run `action` in a temporarily modified scope; restore the original scope
   * when `action` completes (whether normally or via exception).
   */
  private def withScope[A](modify: ResolverEnv => ResolverEnv)(action: => A): A = {
    val saved = env
    env = modify(saved)
    try action
    finally env = saved
  }

  // ---------------------------------------------------------------------------
  // Public API
  // ---------------------------------------------------------------------------

  /** Resolve a full module.  Throws `ResolveError` on failure. */
  def resolveModule(raw: RawModule): ParsedModule = {
    env = ResolverEnv(raw.name, existingNames)
    val (decls, names) = resolveDecls(raw.decls)
    ParsedModule(raw.name, raw.imports, decls, names)
  }

  /** Resolve a standalone expression.  Throws `ResolveError` on failure. */
  def resolveExpression(raw: RawTerm): Term = resolveTerm(raw)

  // ---------------------------------------------------------------------------
  // Declaration resolution
  // ---------------------------------------------------------------------------

  private def resolveDecls(rawDecls: List[RawDecl]): (List[Declarations], List[(Ident, SymKind)]) = {
    var accDecls = List.empty[Declarations]
    var accNames = List.empty[(Ident, SymKind)]
    for (d <- rawDecls) {
      val (decl, names) = resolveDecl(d)
      env = env.insertIdents(names)
      accDecls = accDecls :+ decl
      accNames = accNames ++ names
    }
    (accDecls, accNames)
  }

  private def resolveDecl(d: RawDecl): (Declarations, List[(Ident, SymKind)]) = d match {
    case RawDecl.Def(name, rawTele, ty, body) =>
      val tele  = flattenRawTele(rawTele)
      val rType = resolveBindsPi(tele, ty)
      val rBody = resolveDefBody(name, tele, body)
      val loc   = freshLoc()
      (Declarations.MutualDecls(loc, List((name, (rType, rBody)))), List((name, SymKind.Variable)))

    case RawDecl.Data(name, rawTele, rawLabels) =>
      resolveDeclData(name, rawTele, rawLabels, useHSum = false)

    case RawDecl.HData(name, rawTele, rawLabels) =>
      resolveDeclData(name, rawTele, rawLabels, useHSum = true)

    case RawDecl.Split(name, rawTele, ty, branches) =>
      val tele = flattenRawTele(rawTele)
      val loc  = freshLoc()
      val splitName = env.moduleName + "_L" + loc.line + "_C" + loc.col
      val rType     = resolveBindsPi(tele, ty)
      val rTy       = withScope(_.insertVars(tele.map(_._2)))(resolveTerm(ty))
      val rBranches = withScope(_.insertVars(name :: tele.map(_._2)))(resolveBranches(branches))
      val rTele     = resolveRawTelescope(tele)
      val body      = buildLams(rTele, Term.Split(splitName, loc, rTy, rBranches))
      (Declarations.MutualDecls(loc, List((name, (rType, body)))), List((name, SymKind.Variable)))

    case RawDecl.Undef(name, rawTele, ty) =>
      val tele  = flattenRawTele(rawTele)
      val rType = resolveBindsPi(tele, ty)
      val loc   = freshLoc()
      (Declarations.MutualDecls(loc, List((name, (rType, Term.Undef(loc, rType))))), List((name, SymKind.Variable)))

    case RawDecl.Mutual(rawDecls) =>
      val allNames = rawDecls.flatMap(extractDeclNames)
      withScope(_.insertIdents(allNames)) {
        val pairs = rawDecls.flatMap(resolveNonMutualDecl)
        val loc   = freshLoc()
        (Declarations.MutualDecls(loc, pairs), allNames)
      }

    case RawDecl.Opaque(name)      => (Declarations.OpaqueDecl(name), Nil)
    case RawDecl.Transparent(name) => (Declarations.TransparentDecl(name), Nil)
    case RawDecl.TransparentAll    => (Declarations.TransparentAllDecl, Nil)
  }

  /** Resolve `(x₁ : A₁) → … → (xₙ : Aₙ) → body` where the telescope binds each name into scope. */
  private def resolveBindsPi(tele: List[(Icity, Ident, RawTerm)], body: RawTerm): Term =
    tele match {
      case Nil => resolveTerm(body)
      case (icity, name, ty) :: rest =>
        val rTy    = resolveTerm(ty)
        val rInner = withScope(_.insertVar(name))(resolveBindsPi(rest, body))
        Term.Pi(icity, Term.Lam(icity, name, rTy, rInner))
    }

  /** Resolve `λ x₁ … xₙ → body` where each binder is drawn from a raw telescope. */
  private def resolveLams(tele: List[(Icity, Ident, RawTerm)], body: RawTerm): Term =
    tele match {
      case Nil => resolveTerm(body)
      case (icity, paramName, ty) :: rest =>
        val rTy    = resolveTerm(ty)
        val rInner = withScope(_.insertVar(paramName))(resolveLams(rest, body))
        Term.Lam(icity, paramName, rTy, rInner)
    }

  /**
   * Resolve `λ x₁ … xₙ → (body where { decls })`.
   *
   * The `where`-block `decls` may refer to the telescope parameters `x₁ … xₙ`, so
   * the resolved `Where` node must sit **inside** the lambda chain — not outside.
   * The resulting term has the shape `Lam(x₁, A₁, … Lam(xₙ, Aₙ, Where(body, decls)))`.
   */
  private def resolveLamsWithWhere(
    tele: List[(Icity, Ident, RawTerm)],
    body: RawTerm,
    rawDecls: List[RawDecl]
  ): Term =
    tele match {
      case Nil =>
        val (resolvedDecls, _) = resolveDecls(rawDecls)
        val rb = resolveTerm(body)
        Term.mkWheres(resolvedDecls, rb)
      case (icity, paramName, ty) :: rest =>
        val rTy    = resolveTerm(ty)
        val rInner = withScope(_.insertVar(paramName))(resolveLamsWithWhere(rest, body, rawDecls))
        Term.Lam(icity, paramName, rTy, rInner)
    }

  private def resolveDefBody(name: Ident, tele: List[(Icity, Ident, RawTerm)], body: RawExpWhere): Term =
    body match {
      case RawExpWhere.NoWhere(e) =>
        withScope(_.insertVar(name))(resolveLams(tele, e))
      case RawExpWhere.Where(e, decls) =>
        // All telescope params and the function name are in scope for the where-block
        // and the body.  The Where node must be nested *inside* the lambdas so that
        // the TypeChecker sees the telescope vars in scope when it checks the where
        // declarations.
        withScope(_.insertVar(name)) {
          resolveLamsWithWhere(tele, e, decls)
        }
    }

  private def resolveDeclData(
    name: Ident,
    rawTele: List[(Icity, List[Ident], RawTerm)],
    rawLabels: List[RawLabel],
    useHSum: Boolean
  ): (Declarations, List[(Ident, SymKind)]) = {
    val tele   = flattenRawTele(rawTele)
    val loc    = freshLoc()
    val cs     = rawLabels.collect { case RawLabel.OrdinaryLabel(lbl, _)    => (lbl, SymKind.Constructor: SymKind) }
    val pcs    = rawLabels.collect { case RawLabel.PathLabel(lbl, _, _, _)  => (lbl, SymKind.PConstructor: SymKind) }
    val sumCtor: (Loc, Ident, List[Label]) => Term =
      if (!useHSum && pcs.isEmpty) Term.Sum.apply else Term.HSum.apply

    val rType = resolveBindsPi(tele, RawTerm.U)
    val rBody = withScope(_.insertVar(name)) {
      resolveLabelsWithLams(tele, cs ++ pcs, rawLabels, loc, name, sumCtor)
    }
    val names = (name, SymKind.Variable: SymKind) :: (cs ++ pcs)
    (Declarations.MutualDecls(loc, List((name, (rType, rBody)))), names)
  }

  private def resolveLabelsWithLams(
    tele: List[(Icity, Ident, RawTerm)],
    ctors: List[(Ident, SymKind)],
    rawLabels: List[RawLabel],
    loc: Loc,
    name: Ident,
    sumCtor: (Loc, Ident, List[Label]) => Term
  ): Term =
    tele match {
      case Nil =>
        withScope(_.insertIdents(ctors)) {
          val rLabels = resolveRawLabels(rawLabels)
          sumCtor(loc, name, rLabels)
        }
      case (icity, paramName, ty) :: rest =>
        val rTy    = resolveTerm(ty)
        val rInner = withScope(_.insertVar(paramName)) {
          resolveLabelsWithLams(rest, ctors, rawLabels, loc, name, sumCtor)
        }
        Term.Lam(icity, paramName, rTy, rInner)
    }

  private def extractDeclNames(d: RawDecl): List[(Ident, SymKind)] = d match {
    case RawDecl.Def(name, _, _, _)     => List((name, SymKind.Variable))
    case RawDecl.Data(name, _, labels)  =>
      (name, SymKind.Variable: SymKind) :: labels.map {
        case RawLabel.OrdinaryLabel(lbl, _)    => (lbl, SymKind.Constructor: SymKind)
        case RawLabel.PathLabel(lbl, _, _, _)  => (lbl, SymKind.PConstructor: SymKind)
      }
    case RawDecl.HData(name, _, labels) =>
      (name, SymKind.Variable: SymKind) :: labels.map {
        case RawLabel.OrdinaryLabel(lbl, _)    => (lbl, SymKind.Constructor: SymKind)
        case RawLabel.PathLabel(lbl, _, _, _)  => (lbl, SymKind.PConstructor: SymKind)
      }
    case RawDecl.Split(name, _, _, _)   => List((name, SymKind.Variable))
    case RawDecl.Undef(name, _, _)      => List((name, SymKind.Variable))
    case RawDecl.Mutual(decls)          => decls.flatMap(extractDeclNames)
    case RawDecl.Opaque(_)              => Nil
    case RawDecl.Transparent(_)         => Nil
    case RawDecl.TransparentAll         => Nil
  }

  private def resolveNonMutualDecl(d: RawDecl): List[Declaration] = d match {
    case RawDecl.Def(name, rawTele, ty, body) =>
      val tele  = flattenRawTele(rawTele)
      val rType = resolveBindsPi(tele, ty)
      val rBody = resolveDefBody(name, tele, body)
      List((name, (rType, rBody)))

    case RawDecl.Data(name, rawTele, rawLabels) =>
      val tele    = flattenRawTele(rawTele)
      val loc     = freshLoc()
      val cs      = rawLabels.collect { case RawLabel.OrdinaryLabel(lbl, _)   => (lbl, SymKind.Constructor: SymKind) }
      val pcs     = rawLabels.collect { case RawLabel.PathLabel(lbl, _, _, _) => (lbl, SymKind.PConstructor: SymKind) }
      val sumCtor: (Loc, Ident, List[Label]) => Term = if (pcs.isEmpty) Term.Sum.apply else Term.HSum.apply
      val rType = resolveBindsPi(tele, RawTerm.U)
      val rBody = withScope(_.insertVar(name)) {
        resolveLabelsWithLams(tele, cs ++ pcs, rawLabels, loc, name, sumCtor)
      }
      List((name, (rType, rBody)))

    case RawDecl.HData(name, rawTele, rawLabels) =>
      val tele    = flattenRawTele(rawTele)
      val loc     = freshLoc()
      val cs      = rawLabels.collect { case RawLabel.OrdinaryLabel(lbl, _)   => (lbl, SymKind.Constructor: SymKind) }
      val pcs     = rawLabels.collect { case RawLabel.PathLabel(lbl, _, _, _) => (lbl, SymKind.PConstructor: SymKind) }
      val rType = resolveBindsPi(tele, RawTerm.U)
      val rBody = withScope(_.insertVar(name)) {
        resolveLabelsWithLams(tele, cs ++ pcs, rawLabels, loc, name, Term.HSum.apply)
      }
      List((name, (rType, rBody)))

    case RawDecl.Split(name, rawTele, ty, branches) =>
      val tele = flattenRawTele(rawTele)
      val loc  = freshLoc()
      val splitName = env.moduleName + "_L" + loc.line + "_C" + loc.col
      val rType     = resolveBindsPi(tele, ty)
      val rTy       = withScope(_.insertVars(tele.map(_._2)))(resolveTerm(ty))
      val rBranches = withScope(_.insertVars(name :: tele.map(_._2)))(resolveBranches(branches))
      val rTele     = resolveRawTelescope(tele)
      List((name, (rType, buildLams(rTele, Term.Split(splitName, loc, rTy, rBranches)))))

    case RawDecl.Undef(name, rawTele, ty) =>
      val tele  = flattenRawTele(rawTele)
      val rType = resolveBindsPi(tele, ty)
      val loc   = freshLoc()
      List((name, (rType, Term.Undef(loc, rType))))

    case _ => Nil
  }

  // ---------------------------------------------------------------------------
  // Term resolution
  // ---------------------------------------------------------------------------

  private def resolveTerm(t: RawTerm): Term = {
    val (head, args) = RawTerm.unApps(t)
    head match {
      case RawTerm.Var(x) =>
        env.lookupKind(x) match {
          case Some(SymKind.Variable) =>
            val rArgs = resolveArgs(args)
            if (rArgs.isEmpty) Term.Var(x) else Term.mkAppsIcity(Term.Var(x), rArgs)
          case Some(SymKind.Constructor) =>
            val rArgs = resolveArgs(args).map(_._2)
            Term.Con(x, rArgs)
          case Some(SymKind.PConstructor) =>
            // Path constructor: the first implicit argument is the data type,
            // remaining explicit args are constructor arguments.
            // The formula arguments (@ i j) are handled by AppFormula, not here.
            args match {
              case (Icity.Implicit, dtRaw) :: restArgs =>
                val rDt = resolveTerm(dtRaw)
                val rArgs = restArgs.map { case (_, raw) => resolveTerm(raw) }
                Term.PCon(x, rDt, rArgs, Nil)
              case _ =>
                throw ResolveError(s"Path constructor $x requires a type argument in curly braces: $x {Type}")
            }
          case Some(SymKind.DimName) =>
            throw ResolveError(s"Name $x used as expression")
          case None =>
            throw ResolveError(s"Cannot resolve variable $x in module ${env.moduleName}")
        }
      case _ =>
        val rHead = resolveTermInner(head)
        val rArgs = resolveArgs(args)
        if (rArgs.isEmpty) rHead else Term.mkAppsIcity(rHead, rArgs)
    }
  }

  private def resolveArgs(args: List[(Icity, RawTerm)]): List[(Icity, Term)] =
    args.map { case (icity, raw) => (icity, resolveTerm(raw)) }

  private def resolveTermInner(t: RawTerm): Term = t match {
    case RawTerm.U         => Term.U
    case RawTerm.Var(_)    => resolveTerm(t)
    case RawTerm.App(_, _, _) => resolveTerm(t)

    case RawTerm.Pi(icity, body)    => Term.Pi(icity, resolveTermInner(body))
    case RawTerm.Sigma(body) => Term.Sigma(resolveTermInner(body))

    case RawTerm.Lam(icity, name, ty, body) =>
      val rTy   = resolveTerm(ty)
      val rBody = withScope(_.insertVar(name))(resolveTerm(body))
      Term.Lam(icity, name, rTy, rBody)

    case RawTerm.Pair(a, b) =>
      Term.Pair(resolveTerm(a), resolveTerm(b))

    case RawTerm.Fst(p) => Term.Fst(resolveTerm(p))
    case RawTerm.Snd(p) => Term.Snd(resolveTerm(p))

    case RawTerm.Where(body, decls) =>
      val (rDecls, names) = resolveDecls(decls)
      val rb = withScope(_.insertIdents(names))(resolveTerm(body))
      Term.mkWheres(rDecls, rb)

    case RawTerm.PCon(name, dt, args, phis) =>
      val rDt   = resolveTerm(dt)
      val rArgs = args.map(resolveTerm)
      val rPhis = resolveFormulas(phis)
      Term.PCon(name, rDt, rArgs, rPhis)

    case RawTerm.Split(name, loc, ty, branches) =>
      val rTy       = resolveTerm(ty)
      val rBranches = resolveBranches(branches)
      Term.Split(name, loc, rTy, rBranches)

    case RawTerm.Sum(loc, name, labels) =>
      Term.Sum(loc, name, resolveRawLabels(labels))

    case RawTerm.HSum(loc, name, labels) =>
      Term.HSum(loc, name, resolveRawLabels(labels))

    case RawTerm.UndefinedTerm(loc, ty) =>
      Term.Undef(loc, resolveTerm(ty))

    case RawTerm.Hole(loc) => Term.Hole(loc)

    case RawTerm.PathP(a, u, v) =>
      Term.PathP(resolveTerm(a), resolveTerm(u), resolveTerm(v))

    case RawTerm.PLam(dim, body) =>
      val rb = withScope(_.insertName(dim))(resolveTerm(body))
      Term.PLam(Name(dim), rb)

    case RawTerm.AppFormula(_, _) =>
      val (base, phis) = RawTerm.unAppFormulas(t)
      val (baseHead, baseArgs) = RawTerm.unApps(base)
      baseHead match {
        case RawTerm.PCon(name, dt, pcArgs, _) =>
          val allArgs = pcArgs ::: baseArgs.map(_._2)
          val rDt   = resolveTerm(dt)
          val rArgs = allArgs.map(resolveTerm)
          val rPhis = resolveFormulas(phis)
          Term.PCon(name, rDt, rArgs, rPhis)
        case RawTerm.Var(name) if env.lookupKind(name).contains(SymKind.PConstructor) =>
          baseArgs match {
            case (Icity.Implicit, dtRaw) :: restArgs =>
              val rDt = resolveTerm(dtRaw)
              val rArgs = restArgs.map { case (_, raw) => resolveTerm(raw) }
              val rPhis = resolveFormulas(phis)
              Term.PCon(name, rDt, rArgs, rPhis)
            case _ =>
              throw ResolveError(s"Path constructor $name requires a type argument in curly braces: $name {Type}")
          }
        case _ =>
          val rBase = resolveTerm(base)
          val rPhis = resolveFormulas(phis)
          rPhis.foldLeft(rBase)((acc, phi) => Term.AppFormula(acc, phi))
      }

    case RawTerm.Comp(ty, base, sys) =>
      Term.Comp(resolveTerm(ty), resolveTerm(base), resolveSystem(sys))

    case RawTerm.Fill(ty, base, sys) =>
      Term.Fill(resolveTerm(ty), resolveTerm(base), resolveSystem(sys))

    case RawTerm.HComp(ty, base, sys) =>
      Term.HComp(resolveTerm(ty), resolveTerm(base), resolveSystem(sys))

    case RawTerm.Glue(base, sys) =>
      Term.Glue(resolveTerm(base), resolveSystem(sys))

    case RawTerm.GlueElem(base, sys) =>
      Term.GlueElem(resolveTerm(base), resolveSystem(sys))

    case RawTerm.UnGlueElem(base, sys) =>
      Term.UnGlueElem(resolveTerm(base), resolveSystem(sys))

    case RawTerm.Id(ty, u, v) =>
      Term.Id(resolveTerm(ty), resolveTerm(u), resolveTerm(v))

    case RawTerm.IdPair(w, sys) =>
      Term.IdPair(resolveTerm(w), resolveSystem(sys))

    case RawTerm.IdJ(ty, left, mot, refl, right, path) =>
      Term.IdJ(resolveTerm(ty), resolveTerm(left), resolveTerm(mot),
               resolveTerm(refl), resolveTerm(right), resolveTerm(path))
  }

  // ---------------------------------------------------------------------------
  // Formula resolution
  // ---------------------------------------------------------------------------

  private def resolveFormula(phi: RawFormula): Formula = phi match {
    case RawFormula.Dir(d) => Formula.Dir(d)
    case RawFormula.Atom(x) =>
      env.lookupKind(x) match {
        case Some(SymKind.DimName) => Formula.Atom(Name(x))
        case _                     => throw ResolveError(s"Cannot resolve name $x in module ${env.moduleName}")
      }
    case RawFormula.NegAtom(x) =>
      env.lookupKind(x) match {
        case Some(SymKind.DimName) => Formula.NegAtom(Name(x))
        case _                     => throw ResolveError(s"Cannot resolve name $x in module ${env.moduleName}")
      }
    case RawFormula.And(a, b) => Formula.And(resolveFormula(a), resolveFormula(b))
    case RawFormula.Or(a, b)  => Formula.Or(resolveFormula(a), resolveFormula(b))
  }

  private def resolveFormulas(phis: List[RawFormula]): List[Formula] =
    phis.map(resolveFormula)

  // ---------------------------------------------------------------------------
  // System / face resolution
  // ---------------------------------------------------------------------------

  private def resolveSystem(sys: RawSystem): System[Term] =
    sys.map { case (rawFace, rawTerm) =>
      resolveRawFace(rawFace) -> resolveTerm(rawTerm)
    }

  private def resolveRawFace(rawFace: RawFace): Face =
    rawFace.map { case (x, d) =>
      env.lookupKind(x) match {
        case Some(SymKind.DimName) => Name(x) -> d
        case _ => throw ResolveError(s"Cannot resolve name $x in face constraint in module ${env.moduleName}")
      }
    }

  // ---------------------------------------------------------------------------
  // Branch resolution
  // ---------------------------------------------------------------------------

  private def resolveBranches(branches: List[RawBranch]): List[Branch] =
    branches.map(resolveBranch)

  private def resolveBranch(b: RawBranch): Branch = b match {
    case RawBranch.OrdinaryBranch(ctor, vars, body) =>
      val rb = withScope(_.insertVars(vars))(resolveTerm(body))
      Branch.OrdinaryBranch(ctor, vars, rb)
    case RawBranch.PathBranch(ctor, vars, dims, body) =>
      val rb = withScope(_.insertNames(dims).insertVars(vars))(resolveTerm(body))
      Branch.PathBranch(ctor, vars, dims.map(Name.apply), rb)
  }

  // ---------------------------------------------------------------------------
  // Label resolution
  // ---------------------------------------------------------------------------

  /** Resolve a list of raw (unresolved) constructor labels. */
  private def resolveRawLabels(labels: List[RawLabel]): List[Label] =
    labels.map(resolveRawLabel)

  private def resolveRawLabel(l: RawLabel): Label = l match {
    case RawLabel.OrdinaryLabel(name, rawLabelTele) =>
      val tele = flattenRawLabelTele(rawLabelTele)
      Label.OrdinaryLabel(name, resolveRawLabelTelescope(tele))
    case RawLabel.PathLabel(name, rawLabelTele, dims, rawSys) =>
      val tele = flattenRawLabelTele(rawLabelTele)
      val rt   = resolveRawLabelTelescope(tele)
      val rSys = withScope { e =>
        e.insertNames(dims).insertVars(tele.map(_._1))
      }(resolveSystem(rawSys))
      Label.PathLabel(name, rt, dims.map(Name.apply), rSys)
  }

  // ---------------------------------------------------------------------------
  // Telescope helpers
  // ---------------------------------------------------------------------------

  /**
   * Flatten a declaration telescope `List[(Icity, List[Ident], RawTerm)]` into
   * individual binders `List[(Icity, Ident, RawTerm)]`.
   */
  private def flattenRawTele(tele: List[(Icity, List[Ident], RawTerm)]): List[(Icity, Ident, RawTerm)] =
    tele.flatMap { case (icity, names, ty) => names.map(n => (icity, n, ty)) }

  /**
   * Flatten a constructor-label telescope `List[(List[Ident], RawTerm)]`
   * (which carries no icity) into `List[(Ident, RawTerm)]`.
   */
  private def flattenRawLabelTele(tele: List[(List[Ident], RawTerm)]): List[(Ident, RawTerm)] =
    tele.flatMap { case (names, ty) => names.map(n => (n, ty)) }

  /**
   * Resolve a declaration telescope `List[(Icity, Ident, RawTerm)]` to
   * `List[(Icity, Ident, Term)]`, binding each name into scope for the rest.
   */
  private def resolveRawTelescope(tele: List[(Icity, Ident, RawTerm)]): List[(Icity, Ident, Term)] =
    tele match {
      case Nil => Nil
      case (icity, name, ty) :: rest =>
        val rTy   = resolveTerm(ty)
        val rRest = withScope(_.insertVar(name))(resolveRawTelescope(rest))
        (icity, name, rTy) :: rRest
    }

  /**
   * Resolve a constructor-label telescope `List[(Ident, RawTerm)]` (no icity)
   * to a `Telescope = List[(Ident, Term)]`, binding each name into scope for the rest.
   */
  private def resolveRawLabelTelescope(tele: List[(Ident, RawTerm)]): Telescope =
    tele match {
      case Nil => Nil
      case (name, ty) :: rest =>
        val rTy   = resolveTerm(ty)
        val rRest = withScope(_.insertVar(name))(resolveRawLabelTelescope(rest))
        (name, rTy) :: rRest
    }

  /** Build a lambda chain from a resolved declaration telescope, preserving icity. */
  private def buildLams(tele: List[(Icity, Ident, Term)], body: Term): Term =
    tele.foldRight(body) { case ((icity, name, ty), acc) => Term.Lam(icity, name, ty, acc) }
}

/**
 * Stateless entry point for name resolution.
 *
 * All methods throw `ResolveError` on failure.
 */
object Resolver {
  def forModule(moduleName: String, existingNames: List[(Ident, SymKind)] = Nil): Resolver =
    new Resolver(moduleName, existingNames)

  /** Resolve a full module.  Throws `ResolveError` on failure. */
  def resolveModule(
    raw: RawModule,
    existingNames: List[(Ident, SymKind)] = Nil
  ): ParsedModule =
    new Resolver(raw.name, existingNames).resolveModule(raw)

  /** Resolve a standalone expression.  Throws `ResolveError` on failure. */
  def resolveExpression(
    raw: RawTerm,
    names: List[(Ident, SymKind)] = Nil
  ): Term =
    new Resolver("", names).resolveExpression(raw)
}
