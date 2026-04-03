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
type LabelIdent = String

// Telescope: (x1 : A1) .. (xn : An)
type Telescope = List[(Ident, Term)]

// ============================================================
// Labels (data type constructors)
// ============================================================

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

// ============================================================
// Branches (case split arms)
// ============================================================

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
}

object Term {
  // Decompose applications: t => (head, args)
  def unApps(t: Term): (Term, List[Term]) = {
    def collectApps(acc: List[Term], t: Term): (Term, List[Term]) = t match {
      case App(fun, arg) => collectApps(arg :: acc, fun)
      case _             => (t, acc)
    }
    collectApps(Nil, t)
  }

  // Build nested applications
  def mkApps(head: Term, args: List[Term]): Term = head match {
    case Con(ctor, existingArgs) => Con(ctor, existingArgs ++ args)
    case _                       => args.foldLeft(head)(App.apply)
  }

  // Wrap body in nested Where declarations
  def mkWheres(declsList: List[Declarations], body: Term): Term = declsList match {
    case Nil              => body
    case decl :: restDecls   => Where(mkWheres(restDecls, body), decl)
  }
}
