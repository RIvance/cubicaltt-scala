package cubical

/** Source location for error reporting */
case class Loc(file: String, line: Int, col: Int):
  override def toString: String = s"$file:$line:$col"

object Loc:
  val unknown: Loc = Loc("<unknown>", 0, 0)

/** Variable identifiers */
type Ident = String

/** A telescope: a list of typed binders (x₁:A₁, ..., xₙ:Aₙ) */
type Tele = List[(Ident, Term)]

// ============================================================
// Terms (the surface/core syntax of Cubical TT)
// ============================================================

/** Labels for data type constructors */
enum Label:
  /** Ordinary constructor: c (x₁:A₁) ... (xₙ:Aₙ) */
  case OLabel(name: Ident, tele: Tele)

  /** Path constructor: c (x₁:A₁)... [i₁...iₘ] (sys: System Term) */
  case PLabel(name: Ident, tele: Tele, dims: List[Name], sys: System[Term])

/** Branches in a split/case expression */
enum Branch:
  /** c x₁ ... xₙ → body */
  case OBranch(ctor: Ident, vars: List[Ident], body: Term)
  /** c x₁ ... xₙ i₁ ... iₘ → body  (path branch) */
  case PBranch(ctor: Ident, vars: List[Ident], dims: List[Name], body: Term)

/** Top-level declaration */
enum Decl:
  case DataDecl(name: Ident, params: Tele, ty: Term, constructors: List[(Ident, Term)])
  case DefDecl(name: Ident, ty: Term, body: Term)

/** A group of (possibly mutual) declarations */
enum Decls:
  case MutualDecls(loc: Loc, decls: List[(Ident, (Term, Term))])  // (name, (type, def))
  case OpaqueDecl(name: Ident)
  case TransparentDecl(name: Ident)
  case TransparentAll

object Decls:
  extension (d: Decls)
    def idents: List[Ident] = d match
      case MutualDecls(_, ds) => ds.map(_._1)
      case OpaqueDecl(n)      => List(n)
      case TransparentDecl(n) => List(n)
      case TransparentAll     => Nil

/** The main term AST.
 *
 *  Design note: using a sealed trait + case classes (OOP-style) instead of
 *  a plain Haskell data type. This lets us:
 *    - Add methods to terms (freeVars, subst, pretty-print) directly
 *    - Use pattern matching everywhere we need it
 *    - Keep the algebra open via sealed → exhaustive matches
 */
sealed trait Term:
  import Term.*

  /** Collect free term-variable names (not dimension names) */
  def freeVars: Set[Ident] = this match
    case Var(x)                  => Set(x)
    case Univ                    => Set.empty
    case Pi(a, b)                => a.freeVars ++ b.freeVars
    case Lam(x, ty, body)        => ty.freeVars ++ (body.freeVars - x)
    case App(f, a)               => f.freeVars ++ a.freeVars
    case Sigma(a, b)             => a.freeVars ++ b.freeVars
    case Pair(l, r)              => l.freeVars ++ r.freeVars
    case Fst(p)                  => p.freeVars
    case Snd(p)                  => p.freeVars
    case Con(_, args)            => args.flatMap(_.freeVars).toSet
    case PCon(_, ty, args, _)    => ty.freeVars ++ args.flatMap(_.freeVars)
    case Split(x, _, _, _)       => Set(x) // split is a defined name
    case Sum(_, _, _)            => Set.empty
    case HSum(_, _, _)           => Set.empty
    case PathP(a, u, v)          => a.freeVars ++ u.freeVars ++ v.freeVars
    case PLam(_, body)           => body.freeVars
    case AppFormula(t, _)        => t.freeVars
    case Comp(a, u, sys)         => a.freeVars ++ u.freeVars ++ sys.values.flatMap(_.freeVars)
    case Fill(a, u, sys)         => a.freeVars ++ u.freeVars ++ sys.values.flatMap(_.freeVars)
    case HComp(a, u, sys)        => a.freeVars ++ u.freeVars ++ sys.values.flatMap(_.freeVars)
    case Glue(a, sys)            => a.freeVars ++ sys.values.flatMap(_.freeVars)
    case GlueElem(a, sys)        => a.freeVars ++ sys.values.flatMap(_.freeVars)
    case UnGlueElem(a, sys)      => a.freeVars ++ sys.values.flatMap(_.freeVars)
    case Id(a, u, v)             => a.freeVars ++ u.freeVars ++ v.freeVars
    case IdPair(u, sys)          => u.freeVars ++ sys.values.flatMap(_.freeVars)
    case IdJ(a, u, c, d, x, p)  => Set(a,u,c,d,x,p).flatMap(_.freeVars)
    case Where(t, _)             => t.freeVars  // simplified
    case Undef(_, ty)            => ty.freeVars
    case Hole(_)                 => Set.empty

  def apps(args: List[Term]): Term = args.foldLeft(this)(App.apply)

object Term:
  // ── Core type theory ──────────────────────────────────────
  /** Type universe */
  case object Univ extends Term

  /** Variable reference */
  case class Var(name: Ident) extends Term

  // ── Dependent functions ───────────────────────────────────
  /** Π-type: Pi(A, B) where B is a term with a binder (stored as a Lam) */
  case class Pi(domain: Term, codomain: Term) extends Term
  case class Lam(x: Ident, ty: Term, body: Term) extends Term
  case class App(fun: Term, arg: Term) extends Term

  // ── Dependent pairs ───────────────────────────────────────
  case class Sigma(fstTy: Term, sndTy: Term) extends Term
  case class Pair(fst: Term, snd: Term) extends Term
  case class Fst(pair: Term) extends Term
  case class Snd(pair: Term) extends Term

  // ── Data types ────────────────────────────────────────────
  case class Con(ctor: Ident, args: List[Term]) extends Term
  /** Path constructor application: c A ts phis */
  case class PCon(ctor: Ident, dataType: Term, args: List[Term], phis: List[Formula]) extends Term
  /** Pattern split: split_f loc A [branches] */
  case class Split(name: Ident, loc: Loc, ty: Term, branches: List[Branch]) extends Term
  /** Labelled sum (ordinary data type declaration body) */
  case class Sum(loc: Loc, name: Ident, labels: List[Label]) extends Term
  /** Higher inductive type declaration body */
  case class HSum(loc: Loc, name: Ident, labels: List[Label]) extends Term

  // ── Path types ────────────────────────────────────────────
  /** PathP A u v : the type of paths from u to v over A */
  case class PathP(pathTy: Term, left: Term, right: Term) extends Term
  /** <i> t : path abstraction */
  case class PLam(dim: Name, body: Term) extends Term
  /** t @ φ : path application to a formula */
  case class AppFormula(path: Term, phi: Formula) extends Term

  // ── Kan operations ────────────────────────────────────────
  /** comp A u [sys] : composition */
  case class Comp(ty: Term, base: Term, sys: System[Term]) extends Term
  /** fill A u [sys] : filling */
  case class Fill(ty: Term, base: Term, sys: System[Term]) extends Term
  /** hcomp A u [sys] : homogeneous composition */
  case class HComp(ty: Term, base: Term, sys: System[Term]) extends Term

  // ── Glue types (for univalence) ───────────────────────────
  case class Glue(base: Term, sys: System[Term]) extends Term
  case class GlueElem(base: Term, sys: System[Term]) extends Term
  case class UnGlueElem(base: Term, sys: System[Term]) extends Term

  // ── Identity types ────────────────────────────────────────
  case class Id(ty: Term, left: Term, right: Term) extends Term
  case class IdPair(witness: Term, sys: System[Term]) extends Term
  case class IdJ(ty: Term, left: Term, mot: Term, refl: Term, right: Term, path: Term) extends Term

  // ── Structural ────────────────────────────────────────────
  /** Local definitions: t where decls */
  case class Where(body: Term, decls: Decls) extends Term
  /** Undefined: a typed hole with a known type */
  case class Undef(loc: Loc, ty: Term) extends Term
  /** Untyped hole */
  case class Hole(loc: Loc) extends Term
