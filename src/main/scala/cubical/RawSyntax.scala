package cubical

import scala.collection.immutable.Map as IMap

/**
 * Unresolved face constraint: a partial map from dimension name strings to
 * endpoints `0` or `1`.  Unlike `Face = Map[Name, Dir]`, the keys here are
 * plain strings because dimension names have not yet been verified to be
 * in scope.
 */
type RawFace   = IMap[String, Dir]

/**
 * Unresolved system `[φ₁ ↦ t₁, …, φₙ ↦ tₙ]`.  Keys are `RawFace` (unresolved
 * face constraints) and values are `RawTerm`s.
 */
type RawSystem = IMap[RawFace, RawTerm]

/**
 * Unresolved connective formula over dimension names that have not yet been
 * checked to be in scope.
 *
 * {{{
 *   φ, ψ ::= 0 | 1 | i | -i | φ ∧ ψ | φ ∨ ψ
 * }}}
 *
 * Compared to `Formula`, atoms carry a plain `String` name rather than a
 * resolved `Name`.
 */
enum RawFormula {
  case Dir(dir: cubical.Dir)
  case Atom(name: String)
  case NegAtom(name: String)
  case And(left: RawFormula, right: RawFormula)
  case Or(left: RawFormula, right: RawFormula)
}

/**
 * An unresolved branch (arm) in a `split` expression.
 *
 * Like `Branch`, but the body is a `RawTerm` and dimension variables in
 * `PathBranch` are plain `String`s.
 */
enum RawBranch {
  case OrdinaryBranch(ctor: String, vars: List[String], body: RawTerm)
  case PathBranch(ctor: String, vars: List[String], dims: List[String], body: RawTerm)
}

/**
 * An unresolved constructor label in a `data` or `hdata` declaration.
 *
 * `RawOrdinaryLabel` — a point constructor with a grouped telescope
 * `(x₁ x₂ : A)(y : B)…` (groups not yet flattened).
 *
 * `RawPathLabel` — a path constructor; `dims` are the path dimension
 * variable names as plain strings.
 */
enum RawLabel {
  case OrdinaryLabel(name: String, tele: List[(List[String], RawTerm)])
  case PathLabel(name: String, tele: List[(List[String], RawTerm)], dims: List[String], sys: RawSystem)
}

/**
 * Unresolved definition body, optionally accompanied by a `where` block.
 *
 * `NoWhere(expr)` — a plain expression.
 * `Where(expr, decls)` — expression with local `where` declarations.
 */
enum RawExpWhere {
  case NoWhere(expr: RawTerm)
  case Where(expr: RawTerm, decls: List[RawDecl])
}

/**
 * An unresolved top-level or local declaration, as produced directly by the
 * parser before name resolution.
 *
 * `tele` in `Def`/`Data`/`HData`/`Split`/`Undef` is the raw grouped
 * telescope `[(icity, names, type)]` — groups of names sharing one type annotation,
 * with an icity annotation indicating explicit `(x : A)` vs implicit `{x : A}`.
 * The resolver flattens these.
 */
enum RawDecl {
  case Def(name: String, tele: List[(Icity, List[String], RawTerm)], ty: RawTerm, body: RawExpWhere)
  case Data(name: String, tele: List[(Icity, List[String], RawTerm)], labels: List[RawLabel])
  case HData(name: String, tele: List[(Icity, List[String], RawTerm)], labels: List[RawLabel])
  case Split(name: String, tele: List[(Icity, List[String], RawTerm)], ty: RawTerm, branches: List[RawBranch])
  case Undef(name: String, tele: List[(Icity, List[String], RawTerm)], ty: RawTerm)
  case Mutual(decls: List[RawDecl])
  case Opaque(name: String)
  case Transparent(name: String)
  case TransparentAll
}

/**
 * The result of purely parsing a `.ctt` module, before name resolution.
 *
 * `name` is the module name as written in the source.
 * `imports` is the list of imported module names (strings, not file paths).
 * `decls` is the list of raw (unresolved) top-level declarations.
 */
case class RawModule(name: String, imports: List[String], decls: List[RawDecl])

/**
 * Pre-terms: the raw (unresolved) syntax of Cubical TT as produced by the
 * parser.
 *
 * Every constructor corresponds to a syntactic form.  Names are plain
 * `String`s throughout; no distinction is made between variables,
 * constructors, path constructors, and dimension names — that distinction
 * is established by `Resolver`.
 *
 * Structural correspondence with `Term`:
 *   - `RawVar(x)` →  either `Term.Var(x)`, `Term.Con(x, Nil)`, or an error
 *   - `RawApp` resolves the head first to determine whether to build
 *     `Term.App`, `Term.Con`, or `Term.PCon`
 *   - `RawFormula`/`RawSystem` carry string names; `Resolver` wraps atoms in `Name`
 *
 * Notable encoding: `RawPi(Lam x A B)` and `RawSigma(Lam x A B)` follow
 * the same binder-as-Lam encoding as `Term.Pi`/`Term.Sigma`.
 */
enum RawTerm {
  case U
  case Var(name: String)
  case App(icity: Icity, fun: RawTerm, arg: RawTerm)
  case Pi(icity: Icity, body: RawTerm)                                        // Pi icity (Lam x A B)
  case Lam(icity: Icity, name: String, ty: RawTerm, body: RawTerm)
  case Where(body: RawTerm, decls: List[RawDecl])
  case Sigma(body: RawTerm)                                     // Sigma (Lam x A B)
  case Pair(fst: RawTerm, snd: RawTerm)
  case Fst(pair: RawTerm)
  case Snd(pair: RawTerm)
  case PCon(name: String, dataType: RawTerm, args: List[RawTerm], phis: List[RawFormula])
  case Split(name: String, loc: Loc, ty: RawTerm, branches: List[RawBranch])
  case Sum(loc: Loc, name: String, labels: List[RawLabel])
  case HSum(loc: Loc, name: String, labels: List[RawLabel])
  case UndefinedTerm(loc: Loc, ty: RawTerm)
  case Hole(loc: Loc)
  case PathP(pathTy: RawTerm, left: RawTerm, right: RawTerm)
  case PLam(dim: String, body: RawTerm)
  case AppFormula(path: RawTerm, phi: RawFormula)
  case Comp(ty: RawTerm, base: RawTerm, sys: RawSystem)
  case Fill(ty: RawTerm, base: RawTerm, sys: RawSystem)
  case HComp(ty: RawTerm, base: RawTerm, sys: RawSystem)
  case Glue(base: RawTerm, sys: RawSystem)
  case GlueElem(base: RawTerm, sys: RawSystem)
  case UnGlueElem(base: RawTerm, sys: RawSystem)
  case Id(ty: RawTerm, left: RawTerm, right: RawTerm)
  case IdPair(witness: RawTerm, sys: RawSystem)
  case IdJ(ty: RawTerm, left: RawTerm, mot: RawTerm, refl: RawTerm, right: RawTerm, path: RawTerm)
}

object RawTerm {
  /** Decompose left-nested applications: `f a₁ a₂ … aₙ  ↦  (f, [(ι₁, a₁), …, (ιₙ, aₙ)])`. */
  def unApps(t: RawTerm): (RawTerm, List[(Icity, RawTerm)]) = {
    def go(acc: List[(Icity, RawTerm)], t: RawTerm): (RawTerm, List[(Icity, RawTerm)]) = t match {
      case App(icity, fun, arg) => go((icity, arg) :: acc, fun)
      case _                    => (t, acc)
    }
    go(Nil, t)
  }

  /** Collect a left-nested `AppFormula` chain: `((u φ₁) φ₂) … φₙ  ↦  (u, φ₁…φₙ)`. */
  def unAppFormulas(t: RawTerm): (RawTerm, List[RawFormula]) = {
    def go(acc: List[RawFormula], t: RawTerm): (RawTerm, List[RawFormula]) = t match {
      case AppFormula(path, phi) => go(phi :: acc, path)
      case _                     => (t, acc)
    }
    go(Nil, t)
  }
}
