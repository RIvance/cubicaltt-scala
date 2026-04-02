package cubical

import scala.collection.immutable.Set

// ============================================================
// Values (semantic domain after evaluation)
// ============================================================

enum Val {
  case VU
  case Closure(term: cubical.Term, env: Environment)
  case VPi(domain: Val, codomain: Val)
  case VSigma(fstTy: Val, sndTy: Val)
  case VPair(fst: Val, snd: Val)
  case VCon(name: LIdent, args: List[Val])
  case VPCon(name: LIdent, dataType: Val, args: List[Val], phis: List[Formula])
  case VPathP(pathTy: Val, left: Val, right: Val)
  case VPLam(dim: Name, body: Val)
  case VComp(ty: Val, base: Val, sys: System[Val])
  case VGlue(base: Val, sys: System[Val])
  case VGlueElem(base: Val, sys: System[Val])
  case VUnGlueElem(base: Val, sys: System[Val])
  case VCompU(base: Val, sys: System[Val])
  case VHComp(ty: Val, base: Val, sys: System[Val])
  case VId(ty: Val, left: Val, right: Val)
  case VIdPair(witness: Val, sys: System[Val])
  // Neutral values
  case VVar(name: Ident, ty: Val)
  case VOpaque(name: Ident, ty: Val)
  case VFst(pair: Val)
  case VSnd(pair: Val)
  case VSplit(fun: Val, arg: Val)
  case VApp(fun: Val, arg: Val)
  case VAppFormula(path: Val, phi: Formula)
  case VLam(name: Ident, domain: Val, body: Val)
  case VUnGlueElemU(equiv: Val, base: Val, sys: System[Val])
  case VIdJ(ty: Val, left: Val, mot: Val, refl: Val, right: Val, path: Val)
}

object Val {
  def isNeutral(v: Val): Boolean = v match {
    case Closure(cubical.Term.Undef(_, _), _) => true
    case Closure(cubical.Term.Hole(_), _)     => true
    case VVar(_, _)            => true
    case VOpaque(_, _)         => true
    case VComp(_, _, _)        => true
    case VFst(_)               => true
    case VSnd(_)               => true
    case VSplit(_, _)          => true
    case VApp(_, _)            => true
    case VAppFormula(_, _)     => true
    case VUnGlueElemU(_, _, _) => true
    case VUnGlueElem(_, _)     => true
    case VIdJ(_, _, _, _, _, _) => true
    case _                     => false
  }

  def isNeutralSystem(sys: System[Val]): Boolean = {
    sys.values.exists(isNeutral)
  }

  def mkVar(k: Int, x: String, ty: Val): Val = {
    VVar(x + k.toString, ty)
  }

  def constPath(v: Val): Val = VPLam(Name("_"), v)

  def unCon(v: Val): List[Val] = v match {
    case VCon(_, vs) => vs
    case _           => throw new RuntimeException(s"unCon: not a constructor: $v")
  }
}

// ============================================================
// Environments
// ============================================================

// Context shape: tracks the structure of bindings without values
enum Context {
  case Empty
  case Update(name: Ident, parent: Context)
  case Substitute(dim: Name, parent: Context)
  case Define(loc: Loc, decls: List[Declaration], parent: Context)
}

// The environment: context shape + parallel lists of values and formulas + opaque set
//
// Idents in Context.Update correspond to entries in `vals` (head = most recent)
// Names in Context.Substitute correspond to entries in `formulas` (head = most recent)
// The Nameless set tracks opaque identifiers
case class Environment(
  ctx: Context,
  vals: List[Val],
  formulas: List[Formula],
  opaques: Nameless[Set[Ident]]
)

object Environment {
  val empty: Environment = Environment(Context.Empty, Nil, Nil, Nameless(Set.empty))

  def addDecl(d: Declarations, env: Environment): Environment = d match {
    case Declarations.MutualDecls(m, ds) =>
      Environment(
        Context.Define(m, ds, env.ctx),
        env.vals,
        env.formulas,
        Nameless(env.opaques.value -- Declarations.declIdents(ds).toSet)
      )
    case Declarations.OpaqueDecl(n) =>
      env.copy(opaques = Nameless(env.opaques.value + n))
    case Declarations.TransparentDecl(n) =>
      env.copy(opaques = Nameless(env.opaques.value - n))
    case Declarations.TransparentAllDecl =>
      env.copy(opaques = Nameless(Set.empty))
  }

  def addDeclWhere(d: Declarations, env: Environment): Environment = d match {
    case Declarations.MutualDecls(m, ds) =>
      Environment(
        Context.Define(m, ds, env.ctx),
        env.vals,
        env.formulas,
        Nameless(env.opaques.value -- Declarations.declIdents(ds).toSet)
      )
    case _ => env
  }

  def substitute(iphi: (Name, Formula), env: Environment): Environment = {
    val (i, phi) = iphi
    Environment(Context.Substitute(i, env.ctx), env.vals, phi :: env.formulas, env.opaques)
  }

  def update(xv: (Ident, Val), env: Environment): Environment = {
    val (x, v) = xv
    Environment(
      Context.Update(x, env.ctx),
      v :: env.vals,
      env.formulas,
      Nameless(env.opaques.value - x)
    )
  }

  def updateAll(xvs: List[(Ident, Val)], env: Environment): Environment = {
    xvs.foldLeft(env)((e, xv) => update(xv, e))
  }

  def updateTelescope(tele: Telescope, vs: List[Val], env: Environment): Environment = {
    updateAll(tele.map(_._1).zip(vs), env)
  }

  def substituteAll(iphis: List[(Name, Formula)], env: Environment): Environment = {
    iphis.foldLeft(env)((e, iphi) => substitute(iphi, e))
  }

  def mapEnv(f: Val => Val, g: Formula => Formula, env: Environment): Environment = {
    Environment(env.ctx, env.vals.map(f), env.formulas.map(g), env.opaques)
  }

  def valOfEnv(env: Environment): List[Val] = env.vals

  def formulaOfEnv(env: Environment): List[Formula] = env.formulas

  def domainEnv(env: Environment): List[Name] = {
    def domCtxt(c: Context): List[Name] = c match {
      case Context.Empty              => Nil
      case Context.Update(_, e)       => domCtxt(e)
      case Context.Define(_, _, e)    => domCtxt(e)
      case Context.Substitute(i, e)   => i :: domCtxt(e)
    }
    domCtxt(env.ctx)
  }

  def lookupIdent(x: Ident, env: Environment): Option[Val] = {
    def go(ctx: Context, vs: List[Val], fs: List[Formula], os: Nameless[Set[Ident]]): Option[Val] = ctx match {
      case Context.Empty => None
      case Context.Update(y, parent) =>
        vs match {
          case v :: rest =>
            if (os.value.contains(y)) {
              if (x == y) {
                v match {
                  case Val.VVar(_, ty) => Some(Val.VOpaque(x, ty))
                  case _               => go(parent, rest, fs, os)
                }
              } else {
                go(parent, rest, fs, os)
              }
            } else {
              if (x == y) Some(v) else go(parent, rest, fs, os)
            }
          case Nil => None
        }
      case Context.Substitute(_, parent) =>
        fs match {
          case _ :: rest => go(parent, vs, rest, os)
          case Nil       => None
        }
      case Context.Define(_, decls, parent) =>
        Declarations.declDefs(decls).find(_._1 == x) match {
          case Some((_, body)) =>
            val defEnv = Environment(ctx, vs, fs, os)
            Some(Eval.eval(body, defEnv))
          case None => go(parent, vs, fs, os)
        }
    }
    go(env.ctx, env.vals, env.formulas, env.opaques)
  }

  def lookupName(i: Name, env: Environment): Formula = {
    def go(ctx: Context, vs: List[Val], fs: List[Formula]): Formula = ctx match {
      case Context.Empty => Formula.Atom(i)
      case Context.Update(_, parent) =>
        vs match {
          case _ :: rest => go(parent, rest, fs)
          case Nil       => Formula.Atom(i)
        }
      case Context.Substitute(j, parent) =>
        fs match {
          case phi :: rest => if (i == j) phi else go(parent, vs, rest)
          case Nil         => Formula.Atom(i)
        }
      case Context.Define(_, _, parent) => go(parent, vs, fs)
    }
    go(env.ctx, env.vals, env.formulas)
  }

  def contextOfEnv(env: Environment): List[String] = {
    def go(ctx: Context, vs: List[Val], fs: List[Formula], os: Nameless[Set[Ident]]): List[String] = ctx match {
      case Context.Empty => Nil
      case Context.Update(x, parent) =>
        vs match {
          case (v @ Val.VVar(n, t)) :: rest =>
            s"$n : $t" :: go(parent, rest, fs, os)
          case v :: rest =>
            s"$x = $v" :: go(parent, rest, fs, os)
          case Nil => Nil
        }
      case Context.Define(_, _, parent) => go(parent, vs, fs, os)
      case Context.Substitute(i, parent) =>
        fs match {
          case phi :: rest => s"$i = $phi" :: go(parent, vs, rest, os)
          case Nil         => Nil
        }
    }
    go(env.ctx, env.vals, env.formulas, env.opaques)
  }
}
