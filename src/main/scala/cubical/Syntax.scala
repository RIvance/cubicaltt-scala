package cubical

/**
 * A source location triple used for error reporting.
 *
 * Carried by `Term.Split`, `Term.Sum`, `Term.HSum`, `Term.Undef`, `Term.Hole`,
 * and `Declarations.MutualDecls` so that type errors can point back to the
 * original `.ctt` source position.
 */
case class Loc(file: String, line: Int, col: Int) {
  override def toString: String = s"($line,$col) in $file"
}

object Loc {
  val empty: Loc = Loc("", 0, 0)
}

/**
 * Icity (implicit/explicit) annotation for Π-binders, λ-binders, and applications.
 *
 * {{{
 *   (x : A) → B    Explicit binder
 *   {x : A} → B    Implicit binder — argument inferred by elaboration
 * }}}
 *
 * The name "Icity" follows the Agda convention: it classifies whether an
 * argument position is **i**mpli**cit** or expli**cit**.
 */
enum Icity {
  case Explicit
  case Implicit
}

/**
 * `Ident` — a term-level variable name (e.g. `"x"`, `"f"`).
 *
 * `LabelIdent` — a constructor name in a labelled sum type (e.g. `"zero"`, `"suc"`).
 *
 * `Telescope` — a snoc-list of typed binders `(x₁ : A₁) … (xₙ : Aₙ)` used in
 * constructor declarations and function types.  Each `(x, A)` pair binds `x` in
 * the scope of all subsequent entries (dependent telescope).
 */
type Ident = String
type LabelIdent = String

// Telescope: (x1 : A1) .. (xn : An)
type Telescope = List[(Ident, Term)]

/**
 * A constructor label in a `Sum` or `HSum` declaration.
 *
 * `OrdinaryLabel(c, tele)` — a point constructor `c : tele → D` in an inductive
 * type `D`, where `tele` is the dependent telescope of argument types.
 *
 * `PathLabel(c, tele, dims, sys)` — a path constructor in a higher inductive type.
 * Given arguments `tele` and fresh dimension variables `dims = (i₁, …, iₖ)`, the
 * constructor produces an element of type `D` whose boundary is specified by the
 * system `sys : [φ ↦ t]` (a partial element of `D` over the face lattice of `dims`).
 *
 * {{{
 *   ────────────────────────────── (OrdinaryLabel)
 *   c : (tele) → D
 *
 *   i₁ … iₖ : 𝕀    sys : D [ φ ]
 *   ──────────────────────────────────── (PathLabel)
 *   c : (tele) → (i₁ … iₖ : 𝕀) → D [ φ ↦ sys ]
 * }}}
 */
enum Label {
  case OrdinaryLabel(name: LabelIdent, telescope: Telescope)
  case PathLabel(name: LabelIdent, telescope: Telescope, dims: List[Name], sys: System[Term])
}

object Label {
  def labelTele(label: Label): (LabelIdent, Telescope) = label match {
    case Label.OrdinaryLabel(c, ts)       => (c, ts)
    case Label.PathLabel(c, ts, _, _) => (c, ts)
  }

  def labelName(label: Label): LabelIdent = labelTele(label)._1

  def labelTeles(labels: List[Label]): List[(LabelIdent, Telescope)] = labels.map(labelTele)

  def lookupLabel(ident: LabelIdent, labels: List[Label]): Option[Telescope] = {
    labelTeles(labels).find(_._1 == ident).map(_._2)
  }

  def lookupPathLabel(ident: LabelIdent, labels: List[Label]): Option[(Telescope, List[Name], System[Term])] = {
    labels.collectFirst {
      case Label.PathLabel(y, tele, dims, sys) if ident == y => (tele, dims, sys)
    }
  }
}

/**
 * A branch (arm) in a `split` expression.
 *
 * `OrdinaryBranch(c, vars, body)` — matches an ordinary constructor `c` applied to
 * `vars`; `body` is checked at the corresponding return type.
 *
 * `PathBranch(c, vars, dims, body)` — matches a path constructor `c`; `vars` bind
 * the point arguments and `dims` bind the path dimensions.  The body must agree
 * with the image of the split function on the boundary `sys` of the constructor.
 */
enum Branch {
  case OrdinaryBranch(ctor: LabelIdent, vars: List[Ident], body: Term)
  case PathBranch(ctor: LabelIdent, vars: List[Ident], dims: List[Name], body: Term)
}

object Branch {
  def branchName(branch: Branch): LabelIdent = branch match {
    case Branch.OrdinaryBranch(c, _, _)    => c
    case Branch.PathBranch(c, _, _, _) => c
  }

  def lookupBranch(ident: LabelIdent, branches: List[Branch]): Option[Branch] = {
    branches.find(branch => branchName(branch) == ident)
  }
}

/**
 * A single mutual declaration block entry `(x, (A, t))` meaning `x : A = t`.
 *
 * `Declarations` wraps one or more `Declaration` entries together with pragmas
 * that control unfolding behaviour:
 *
 *   - `MutualDecls(loc, decls)` — a block of mutually recursive definitions,
 *     processed together so that each `x` is in scope for the bodies of the others.
 *   - `OpaqueDecl(x)` — mark `x` opaque: calls to `x` no longer reduce.
 *     The environment still carries its value for conversion purposes.
 *   - `TransparentDecl(x)` — undo a previous `opaque x`.
 *   - `TransparentAllDecl` — make all names transparent again.
 */
type Declaration = (Ident, (Term, Term))

enum Declarations {
  case MutualDecls(loc: Loc, decls: List[Declaration])
  case OpaqueDecl(name: Ident)
  case TransparentDecl(name: Ident)
  case TransparentAllDecl
}

object Declarations {
  def declIdents(decls: List[Declaration]): List[Ident] = decls.map(_._1)

  def declTerms(decls: List[Declaration]): List[Term] = decls.map(_._2._2)

  def declTelescope(decls: List[Declaration]): Telescope = decls.map { case (x, (t, _)) => (x, t) }

  def declDefs(decls: List[Declaration]): List[(Ident, Term)] = decls.map { case (x, (_, d)) => (x, d) }
}

/**
 * Pre-terms: the raw syntax of Cubical TT before evaluation.
 *
 * Every `Term` constructor corresponds to a syntactic form from the paper.
 * Evaluation (`Eval.eval`) turns a `Term` into a `Val`; the type checker works
 * on `Term`s and calls `eval` at the leaves.
 *
 * Notable encoding choices:
 *   - `Pi(Lam(x, A, B))` and `Sigma(Lam(x, A, B))` encode binders uniformly via
 *     a `Lam` sub-term — the binder name, domain, and codomain share one node.
 *   - `Split`, `Sum`, `HSum`, `Undef`, `Hole` evaluate to `Closure`s, not to
 *     eliminators or types directly.
 *   - `Comp`/`Fill`/`HComp` correspond to the three composition primitives.
 *   - `Glue`/`GlueElem`/`UnGlueElem` are the Glue type and its intro/elim forms.
 *   - `Id`/`IdPair`/`IdJ` are the Swan identity type and its intro/elim forms.
 *
 * Typing highlights:
 * {{{
 *   Γ ⊢ A : U    Γ, x:A ⊢ B : U
 *   ──────────────────────────────── (Π)    ──────────────────────────────── (Σ)
 *   Γ ⊢ (x : A) → B : U                    Γ ⊢ (x : A) × B : U
 *
 *   Γ, i:𝕀 ⊢ A : U    Γ ⊢ a₀ : A 0    Γ ⊢ a₁ : A 1
 *   ──────────────────────────────────────────────────── (PathP)
 *   Γ ⊢ PathP A a₀ a₁ : U
 *
 *   Γ, i:𝕀 ⊢ A : U    Γ ⊢ u₀ : A 0    Γ, i:𝕀 ⊢ [φ ↦ u] : A[φ]
 *   ─────────────────────────────────────────────────────────────── (Comp)
 *   Γ ⊢ comp A [φ ↦ u] u₀ : A 1
 * }}}
 */
enum Term {
  case U
  case Var(name: Ident)
  case App(icity: Icity, fun: Term, arg: Term)
  case Pi(icity: Icity, body: Term)                      // Pi icity (Lam x a b)
  case Lam(icity: Icity, name: Ident, ty: Term, body: Term)
  case Where(body: Term, decls: Declarations)
  case Meta(id: Int)
  case Sigma(body: Term)                                 // Sigma (Lam x a b)
  case Pair(fst: Term, snd: Term)
  case Fst(pair: Term)
  case Snd(pair: Term)
  case Con(name: LabelIdent, args: List[Term])
  case PCon(name: LabelIdent, dataType: Term, args: List[Term], phis: List[Formula])
  case Split(name: Ident, loc: Loc, ty: Term, branches: List[Branch])
  case Sum(loc: Loc, name: Ident, labels: List[Label])
  case HSum(loc: Loc, name: Ident, labels: List[Label])
  case Undef(loc: Loc, ty: Term)
  case Hole(loc: Loc)
  case PathP(pathTy: Term, left: Term, right: Term)
  case PLam(dim: Name, body: Term)
  case AppFormula(path: Term, phi: Formula)
  case Comp(ty: Term, base: Term, sys: System[Term])
  case Fill(ty: Term, base: Term, sys: System[Term])
  case HComp(ty: Term, base: Term, sys: System[Term])
  case Glue(base: Term, sys: System[Term])
  case GlueElem(base: Term, sys: System[Term])
  case UnGlueElem(base: Term, sys: System[Term])
  case Id(ty: Term, left: Term, right: Term)
  case IdPair(witness: Term, sys: System[Term])
  case IdJ(ty: Term, left: Term, mot: Term, refl: Term, right: Term, path: Term)

  // Pretty-printer helpers (precedence-aware, inlined into the enum)
  private def parens(cond: Boolean, s: String): String = if (cond) s"($s)" else s

  private def formatSystem(sys: System[Term]): String = if (sys.isEmpty) "[]" else "[ " + sys.toList.map { case (alpha, u) => s"${Face.showFace(alpha)} ↦ $u" }.mkString(", ") + " ]"

  private def format(prec: Int): String = this match {
    case U => "𝒰"
    case Var(x) => x
    case App(_, _, _) => {
      val (head, args) = Term.unApps(this)
      val ppArgs = args.map {
        case (Icity.Implicit, a) => s"{$a}"
        case (Icity.Explicit, a) => a.format(3)
      }
      parens(prec > 2, (head.format(2) :: ppArgs).mkString(" "))
    }
    case Pi(_, Lam(_, x, a, b)) if x == "_" => parens(prec > 1, s"${a.format(2)} → ${b.format(0)}")
    case Pi(Icity.Implicit, Lam(_, x, a, b)) => parens(prec > 0, s"Π {$x : $a} → ${b.format(0)}")
    case Pi(_, Lam(_, x, a, b)) => parens(prec > 0, s"Π ($x : $a) → ${b.format(0)}")
    case Pi(_, body) => parens(prec > 0, s"Π ${body.format(3)}")
    case Lam(Icity.Implicit, x, a, b) => parens(prec > 0, s"λ {$x : $a}. ${b.format(0)}")
    case Lam(_, x, a, b) => parens(prec > 0, s"λ ($x : $a). ${b.format(0)}")
    case Where(body, decls) => parens(prec > 0, s"${body.format(0)} where ...")
    case Meta(id) => s"?$id"
    case Sigma(Lam(_, x, a, b)) if x == "_" => parens(prec > 1, s"${a.format(2)} × ${b.format(1)}")
    case Sigma(Lam(_, x, a, b)) => parens(prec > 0, s"Σ ($x : $a) × ${b.format(0)}")
    case Sigma(body) => parens(prec > 0, s"Σ ${body.format(3)}")
    case Pair(fst, snd) => s"⟨$fst, $snd⟩"
    case Fst(pair) => s"${pair.format(3)}.1"
    case Snd(pair) => s"${pair.format(3)}.2"
    case Con(name, Nil) => name
    case Con(name, args) => parens(prec > 2, s"$name ${args.map(_.format(3)).mkString(" ")}")
    case PCon(name, dataType, args, phis) => parens(prec > 2, (name :: (args.map(_.format(3)) ++ phis.map(_.toString))).mkString(" "))
    case Split(name, _, ty, branches) => parens(prec > 2, s"split { ... }")
    case Sum(_, name, labels) => parens(prec > 2, s"sum { ... }")
    case HSum(_, name, labels) => parens(prec > 2, s"hsum { ... }")
    case Undef(_, ty) => "undefined"
    case Hole(_) => "_"
    case PathP(pathTy, left, right) => parens(prec > 2, s"PathP ${pathTy.format(3)} ${left.format(3)} ${right.format(3)}")
    case PLam(dim, body) => parens(prec > 0, s"λ̂ ${dim.value}. ${body.format(0)}")
    case AppFormula(path, phi) => parens(prec > 2, s"${path.format(2)} @ $phi")
    case Comp(ty, base, sys) => parens(prec > 2, s"comp ${ty.format(3)} ${base.format(3)} ${formatSystem(sys)}")
    case Fill(ty, base, sys) => parens(prec > 2, s"fill ${ty.format(3)} ${base.format(3)} ${formatSystem(sys)}")
    case HComp(ty, base, sys) => parens(prec > 2, s"hComp ${ty.format(3)} ${base.format(3)} ${formatSystem(sys)}")
    case Glue(base, sys) => parens(prec > 2, s"Glue ${base.format(3)} ${formatSystem(sys)}")
    case GlueElem(base, sys) => parens(prec > 2, s"glue ${base.format(3)} ${formatSystem(sys)}")
    case UnGlueElem(base, sys) => parens(prec > 2, s"unglue ${base.format(3)} ${formatSystem(sys)}")
    case Id(ty, left, right) => parens(prec > 2, s"Id ${ty.format(3)} ${left.format(3)} ${right.format(3)}")
    case IdPair(w, sys) => parens(prec > 2, s"idC ${w.format(3)} ${formatSystem(sys)}")
    case IdJ(ty, left, mot, refl, right, path) => parens(prec > 2, s"idJ ${ty.format(3)} ${left.format(3)} ${mot.format(3)} ${refl.format(3)} ${right.format(3)} ${path.format(3)}")
  }

  override def toString: String = format(0)
}

object Term {
  /** Decompose left-nested applications: `f a₁ a₂ … aₙ  ↦  (f, [(icity₁, a₁), …, (icityₙ, aₙ)])`. */
  def unApps(t: Term): (Term, List[(Icity, Term)]) = {
    def collectApps(acc: List[(Icity, Term)], t: Term): (Term, List[(Icity, Term)]) = t match {
      case App(icity, fun, arg) => collectApps((icity, arg) :: acc, fun)
      case _                    => (t, acc)
    }
    collectApps(Nil, t)
  }

  /** Build left-nested explicit applications `f a₁ … aₙ` from a head and argument list. */
  def mkApps(head: Term, args: List[Term]): Term = head match {
    case Con(ctor, existingArgs) => Con(ctor, existingArgs ++ args)
    case _                       => args.foldLeft(head)(App(Icity.Explicit, _, _))
  }

  /** Build left-nested applications with icity annotations from a head and `(icity, arg)` list. */
  def mkAppsIcity(head: Term, args: List[(Icity, Term)]): Term = head match {
    case Con(ctor, existingArgs) => Con(ctor, existingArgs ++ args.map(_._2))
    case _                       => args.foldLeft(head) { case (acc, (icity, arg)) => App(icity, acc, arg) }
  }

  /** Wrap `body` in a right-nested chain of `Where` declarations. */
  def mkWheres(declsList: List[Declarations], body: Term): Term = declsList match {
    case Nil              => body
    case decl :: restDecls   => Where(mkWheres(restDecls, body), decl)
  }
}
