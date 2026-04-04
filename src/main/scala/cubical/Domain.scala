package cubical

import scala.collection.immutable.Set

/**
 * The semantic domain: values produced by evaluation.
 *
 * Every term evaluates to a `Val`; types are also `Val`s (see `type Type = Val`).
 * The constructors fall into three groups:
 *
 *   - canonical forms (introductions): `VU`, `VPi`, `VSigma`, `VPair`, `VCon`, `VPCon`,
 *     `VPathP`, `VPLam`, `VGlue`, `VGlueElem`, `VId`, `VIdPair`, `VLam`, `Closure`
 *   - computed/stuck compositions: `VComp`, `VHComp`, `VUnGlueElem`, `VCompU`, `VUnGlueElemU`
 *   - neutral values (blocked on a free variable): `VVar`, `VOpaque`, `VFst`, `VSnd`,
 *     `VSplit`, `VApp`, `VAppFormula`, `VIdJ`
 */
enum Val {
  private def parens(cond: Boolean, s: String): String = if (cond) s"($s)" else s

  
  private def formatSystem(sys: System[Val]): String = {
    if (sys.isEmpty) "[]"
    else {
      val parts = sys.toList.map { case (alpha, u) => s"${Face.showFace(alpha)} ↦ $u" }
      "[ " + parts.mkString(", ") + " ]"
    }
  }

  
  private def format(prec: Int): String = this match {
    case VU => "𝒰"
    case Closure(term, _) => term.toString
    case VPi(Icity.Implicit, domain, Closure(Term.Lam(_, x, _, body), _)) =>
      parens(prec > 0, s"Π {$x : ${domain}} → ${body}")
    case VPi(_, domain, Closure(Term.Lam(_, x, _, body), _)) if x == "_" =>
      parens(prec > 1, s"${domain.format(2)} → ${body}")
    case VPi(_, domain, codomain) =>
      parens(prec > 0, s"Π ${domain.format(3)} ${codomain.format(3)}")
    case VSigma(fstTy, Closure(Term.Lam(_, x, _, body), _)) if x == "_" =>
      parens(prec > 1, s"${fstTy.format(2)} × ${body}")
    case VSigma(fstTy, sndTy) => parens(prec > 0, s"Σ ${fstTy.format(3)} ${sndTy.format(3)}")
    case VPair(a, b) => s"⟨${a}, ${b}⟩"
    case VMeta(id) => s"?$id"
    case VCon(c, Nil) => c
    case VCon(c, args) => parens(prec > 2, s"$c ${args.map(_.format(3)).mkString(" ")}")
    case VPCon(c, _dataType, args, phis) =>
      parens(prec > 2, (c :: (args.map(_.format(3)) ++ phis.map(_.toString))).mkString(" "))
    case VPathP(pathTy, left, right) => parens(prec > 2, s"PathP ${pathTy.format(3)} ${left.format(3)} ${right.format(3)}")
    case VPLam(dim, body) => parens(prec > 0, s"λ̂ ${dim.value}. ${body}")
    case VComp(ty, base, sys) => parens(prec > 2, s"comp ${ty.format(3)} ${base.format(3)} ${formatSystem(sys)}")
    case VGlue(base, sys) => parens(prec > 2, s"Glue ${base.format(3)} ${formatSystem(sys)}")
    case VGlueElem(base, sys) => parens(prec > 2, s"glue ${base.format(3)} ${formatSystem(sys)}")
    case VUnGlueElem(base, sys) => parens(prec > 2, s"unglue ${base.format(3)} ${formatSystem(sys)}")
    case VCompU(base, sys) => parens(prec > 2, s"compU ${base.format(3)} ${formatSystem(sys)}")
    case VHComp(ty, base, sys) => parens(prec > 2, s"hComp ${ty.format(3)} ${base.format(3)} ${formatSystem(sys)}")
    case VId(ty, l, r) => parens(prec > 2, s"Id ${ty.format(3)} ${l.format(3)} ${r.format(3)}")
    case VIdPair(w, sys) => parens(prec > 2, s"idC ${w.format(3)} ${formatSystem(sys)}")
    case VVar(name, _) => name
    case VOpaque(name, _) => s"@$name"
    case VFst(p) => s"${p.format(3)}.1"
    case VSnd(p) => s"${p.format(3)}.2"
    case VSplit(f, arg) => parens(prec > 2, s"${f.format(2)} ${arg.format(3)}")
    case VApp(f, arg) => parens(prec > 2, s"${f.format(2)} ${arg.format(3)}")
    case VAppFormula(path, phi) => parens(prec > 2, s"${path.format(2)} @ ${phi}")
    case VLam(x, domain, body) => parens(prec > 0, s"λ $x. ${body}")
    case VUnGlueElemU(equiv, base, sys) => parens(prec > 2, s"unglueU ${equiv.format(3)} ${base.format(3)} ${formatSystem(sys)}")
    case VIdJ(a, l, mot, refl, r, p) => parens(prec > 2, s"idJ ${a.format(3)} ${l.format(3)} ${mot.format(3)} ${refl.format(3)} ${r.format(3)} ${p.format(3)}")
  }

  override def toString: String = format(0)
  case VU
  case Closure(term: Term, env: Environment)
  case VPi(icity: Icity, domain: Type, codomain: Type)
  case VSigma(fstTy: Type, sndTy: Type)
  case VPair(fst: Val, snd: Val)
  case VCon(name: LabelIdent, args: List[Val])
  case VPCon(name: LabelIdent, dataType: Type, args: List[Val], phis: List[Formula])
  case VPathP(pathTy: Type, left: Val, right: Val)
  case VPLam(dim: Name, body: Val)
  case VComp(ty: Type, base: Val, sys: System[Val])
  case VGlue(base: Type, sys: System[Val])
  case VGlueElem(base: Val, sys: System[Val])
  case VUnGlueElem(base: Val, sys: System[Val])
  case VCompU(base: Type, sys: System[Val])
  case VHComp(ty: Type, base: Val, sys: System[Val])
  case VId(ty: Type, left: Val, right: Val)
  case VIdPair(witness: Val, sys: System[Val])
  // Neutral values
  case VVar(name: Ident, ty: Type)
  case VOpaque(name: Ident, ty: Type)
  case VFst(pair: Val)
  case VSnd(pair: Val)
  case VSplit(fun: Val, arg: Val)
  case VApp(fun: Val, arg: Val)
  case VAppFormula(path: Val, phi: Formula)
  case VLam(name: Ident, domain: Type, body: Val)
  case VUnGlueElemU(equiv: Val, base: Type, sys: System[Val])
  case VIdJ(ty: Type, left: Val, mot: Val, refl: Val, right: Val, path: Val)
  // Metavariable (existential, solved during elaboration)
  case VMeta(id: Int)
}

/**
 * Type alias: a `Type` is a `Val` that classifies other values.
 */
type Type = Val

object Val {
  def isNeutral(v: Val): Boolean = v match {
    case Closure(Term.Undef(_, _), _) => true
    case Closure(Term.Hole(_), _)     => true
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
    case VMeta(_)              => true
    case _                     => false
  }

  def isNeutralSystem(sys: System[Val]): Boolean = {
    sys.values.exists(isNeutral)
  }

  def mkVar(counter: Int, varName: String, ty: Type): Val = {
    VVar(varName + counter.toString, ty)
  }

  def constPath(v: Val): Val = VPLam(Name("_"), v)

  def unCon(v: Val): List[Val] = v match {
    case VCon(_, vs) => vs
    case _           => throw new RuntimeException(s"unCon: not a constructor: $v")
  }
}

/**
 * The shape of a typing context, without the runtime values.
 *
 * The context tracks the binding structure; the actual values live in
 * `Environment.vals` and `Environment.formulas` in parallel lists.
 *
 *   - `Empty`      — the empty context  Γ = ·
 *   - `Update`     — term variable binding  Γ, x : A
 *   - `Substitute` — dimension variable binding  Γ, i : 𝕀
 *   - `Define`     — mutually recursive definitions  Γ, {fᵢ : Aᵢ = tᵢ}
 */
enum Context {
  case Empty
  case Update(name: Ident, parent: Context)
  case Substitute(dim: Name, parent: Context)
  case Define(loc: Loc, decls: List[Declaration], parent: Context)
}

/**
 * The runtime environment: context shape paired with parallel value/formula lists.
 *
 * Invariants:
 *   - Each `Context.Update(x, _)` corresponds to the head of `vals`.
 *   - Each `Context.Substitute(i, _)` corresponds to the head of `formulas`.
 *   - `opaques` records which identifiers are currently opaque (blocked).
 */
case class Environment(
  ctx: Context,
  vals: List[Val],
  formulas: List[Formula],
  opaques: Nameless[Set[Ident]]
)

object Environment {
  val empty: Environment = Environment(Context.Empty, Nil, Nil, Nameless(Set.empty))

  def addDecl(d: Declarations, env: Environment): Environment = d match {
    case Declarations.MutualDecls(loc, declPairs) =>
      Environment(
        Context.Define(loc, declPairs, env.ctx),
        env.vals,
        env.formulas,
        Nameless(env.opaques.value -- Declarations.declIdents(declPairs).toSet)
      )
    case Declarations.OpaqueDecl(n) =>
      env.copy(opaques = Nameless(env.opaques.value + n))
    case Declarations.TransparentDecl(n) =>
      env.copy(opaques = Nameless(env.opaques.value - n))
    case Declarations.TransparentAllDecl =>
      env.copy(opaques = Nameless(Set.empty))
  }

  def addDeclWhere(d: Declarations, env: Environment): Environment = d match {
    case Declarations.MutualDecls(loc, declPairs) =>
      Environment(
        Context.Define(loc, declPairs, env.ctx),
        env.vals,
        env.formulas,
        Nameless(env.opaques.value -- Declarations.declIdents(declPairs).toSet)
      )
    case _ => env
  }

  def substitute(nameFormulaPair: (Name, Formula), env: Environment): Environment = {
    val (i, phi) = nameFormulaPair
    Environment(Context.Substitute(i, env.ctx), env.vals, phi :: env.formulas, env.opaques)
  }

  def update(identValPair: (Ident, Val), env: Environment): Environment = {
    val (x, v) = identValPair
    Environment(
      Context.Update(x, env.ctx),
      v :: env.vals,
      env.formulas,
      Nameless(env.opaques.value - x)
    )
  }

  def updateAll(identValPairs: List[(Ident, Val)], env: Environment): Environment = {
    identValPairs.foldLeft(env)((e, identValPair) => update(identValPair, e))
  }

  def updateTelescope(tele: Telescope, vs: List[Val], env: Environment): Environment = {
    updateAll(tele.map(_._1).zip(vs), env)
  }

  def substituteAll(nameFormulaPairs: List[(Name, Formula)], env: Environment): Environment = {
    nameFormulaPairs.foldLeft(env)((e, nameFormulaPair) => substitute(nameFormulaPair, e))
  }

  def mapEnv(f: Val => Val, g: Formula => Formula, env: Environment): Environment = {
    Environment(env.ctx, env.vals.map(f), env.formulas.map(g), env.opaques)
  }

  def valOfEnv(env: Environment): List[Val] = env.vals

  def formulaOfEnv(env: Environment): List[Formula] = env.formulas

  def domainEnv(env: Environment): List[Name] = {
  def domCtxt(ctx: Context): List[Name] = ctx match {
    case Context.Empty              => Nil
    case Context.Update(_, parent) => domCtxt(parent)
    case Context.Define(_, _, parent) => domCtxt(parent)
    case Context.Substitute(i, parent)   => i :: domCtxt(parent)
  }
    domCtxt(env.ctx)
  }

  def lookupIdent(x: Ident, env: Environment): Option[Val] = {
    def go(ctx: Context, vals: List[Val], formulas: List[Formula], opaques: Nameless[Set[Ident]]): Option[Val] = ctx match {
      case Context.Empty => None
      case Context.Update(y, parent) =>
        vals match {
          case v :: rest =>
            if (opaques.value.contains(y)) {
              if (x == y) {
                v match {
                  case Val.VVar(_, ty) => Some(Val.VOpaque(x, ty))
                  case _               => go(parent, rest, formulas, opaques)
                }
              } else {
                go(parent, rest, formulas, opaques)
              }
            } else {
              if (x == y) Some(v) else go(parent, rest, formulas, opaques)
            }
          case Nil => None
        }
      case Context.Substitute(_, parent) =>
        formulas match {
          case _ :: rest => go(parent, vals, rest, opaques)
          case Nil       => None
        }
      case Context.Define(_, decls, parent) =>
        Declarations.declDefs(decls).find(_._1 == x) match {
          case Some((_, body)) =>
            val defEnv = Environment(ctx, vals, formulas, opaques)
            Some(Eval.eval(body, defEnv))
          case None => go(parent, vals, formulas, opaques)
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
    def go(ctx: Context, vals: List[Val], formulas: List[Formula], opaques: Nameless[Set[Ident]]): List[String] = ctx match {
      case Context.Empty => Nil
      case Context.Update(x, parent) =>
        vals match {
          case (v @ Val.VVar(n, t)) :: rest =>
            s"$n : $t" :: go(parent, rest, formulas, opaques)
          case v :: rest =>
            s"$x = $v" :: go(parent, rest, formulas, opaques)
          case Nil => Nil
        }
      case Context.Define(_, _, parent) => go(parent, vals, formulas, opaques)
      case Context.Substitute(i, parent) =>
        formulas match {
          case phi :: rest => s"$i = $phi" :: go(parent, vals, rest, opaques)
          case Nil         => Nil
        }
    }
    go(env.ctx, env.vals, env.formulas, env.opaques)
  }
}
