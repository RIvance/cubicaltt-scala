package cubical

// ============================================================
// Source locations
// ============================================================

case class Loc(file: String, line: Int, col: Int) {
  override def toString: String = s"($line,$col) in $file"
}

object Loc {
  val empty: Loc = Loc("", 0, 0)
}

// ============================================================
// Identifiers
// ============================================================

type Ident = String
type LIdent = String

// Telescope: (x1 : A1) .. (xn : An)
type Telescope = List[(Ident, Term)]

// ============================================================
// Labels (data type constructors)
// ============================================================

enum Label {
  case OLabel(name: LIdent, telescope: Telescope)
  case PLabel(name: LIdent, telescope: Telescope, dims: List[Name], sys: System[Term])
}

object Label {
  def labelTele(l: Label): (LIdent, Telescope) = l match {
    case Label.OLabel(c, ts)       => (c, ts)
    case Label.PLabel(c, ts, _, _) => (c, ts)
  }

  def labelName(l: Label): LIdent = labelTele(l)._1

  def labelTeles(ls: List[Label]): List[(LIdent, Telescope)] = ls.map(labelTele)

  def lookupLabel(x: LIdent, ls: List[Label]): Option[Telescope] = {
    labelTeles(ls).find(_._1 == x).map(_._2)
  }

  def lookupPLabel(x: LIdent, ls: List[Label]): Option[(Telescope, List[Name], System[Term])] = {
    ls.collectFirst {
      case Label.PLabel(y, ts, is, es) if x == y => (ts, is, es)
    }
  }
}

// ============================================================
// Branches (case split arms)
// ============================================================

enum Branch {
  case OBranch(ctor: LIdent, vars: List[Ident], body: Term)
  case PBranch(ctor: LIdent, vars: List[Ident], dims: List[Name], body: Term)
}

object Branch {
  def branchName(b: Branch): LIdent = b match {
    case Branch.OBranch(c, _, _)    => c
    case Branch.PBranch(c, _, _, _) => c
  }

  def lookupBranch(x: LIdent, bs: List[Branch]): Option[Branch] = {
    bs.find(b => branchName(b) == x)
  }
}

// ============================================================
// Declarations
// ============================================================

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

// ============================================================
// Terms (the core syntax of Cubical TT)
// ============================================================

enum Term {
  case U
  case Var(name: Ident)
  case App(fun: Term, arg: Term)
  case Pi(body: Term)                                    // Pi (Lam x a b)
  case Lam(name: Ident, ty: Term, body: Term)
  case Where(body: Term, decls: Declarations)
  case Sigma(body: Term)                                 // Sigma (Lam x a b)
  case Pair(fst: Term, snd: Term)
  case Fst(pair: Term)
  case Snd(pair: Term)
  case Con(name: LIdent, args: List[Term])
  case PCon(name: LIdent, dataType: Term, args: List[Term], phis: List[Formula])
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
}

object Term {
  // Decompose applications: t => (head, args)
  def unApps(t: Term): (Term, List[Term]) = {
    def aux(acc: List[Term], t: Term): (Term, List[Term]) = t match {
      case App(r, s) => aux(s :: acc, r)
      case _         => (t, acc)
    }
    aux(Nil, t)
  }

  // Build nested applications
  def mkApps(t: Term, ts: List[Term]): Term = t match {
    case Con(l, us) => Con(l, us ++ ts)
    case _          => ts.foldLeft(t)(App.apply)
  }

  // Wrap body in nested Where declarations
  def mkWheres(ds: List[Declarations], e: Term): Term = ds match {
    case Nil     => e
    case d :: ds => Where(mkWheres(ds, e), d)
  }
}
