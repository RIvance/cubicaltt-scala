package cubical

import scala.collection.immutable.Map
import Val.*
import Branch.{OrdinaryBranch, PathBranch}

import scala.annotation.tailrec

object Eval {

  /**
   * Look up the value bound to term variable `x` in `env`.
   *
   * Traverses the context spine; when `x` is found under a `Define` node the
   * definition body is evaluated on the spot (lazy unfolding).
   *
   * Throws `EvalError` if `x` is not in scope.
   */
  def lookupVal(x: String, env: Environment): Val = {
    @tailrec
    def loop(ctx: Context, vals: List[Val], formulas: List[Formula], opaques: Nameless[Set[Ident]]): Val = ctx match {
      case Context.Empty => throw EvalError(s"lookupVal: not found $x")
      case Context.Update(y, parent) =>
        vals match {
          case v :: rest => if (x == y) v else loop(parent, rest, formulas, opaques)
          case Nil       => throw EvalError(s"lookupVal: env out of sync for $x")
        }
      case Context.Define(loc, decls, parent) =>
        Declarations.declDefs(decls).find(_._1 == x) match {
          case Some((_, t)) => eval(t, Environment(ctx, vals, formulas, opaques))
          case None         => loop(parent, vals, formulas, opaques)
        }
      case Context.Substitute(_, parent) =>
        formulas match {
          case _ :: rest => loop(parent, vals, rest, opaques)
          case Nil       => throw EvalError(s"lookupVal: env out of sync for $x (Substitute)")
        }
    }
    loop(env.ctx, env.vals, env.formulas, env.opaques)
  }

  /**
   * Look up the declared type of term variable `x` in `env`.
   *
   * Only succeeds for variables that were introduced as `VVar(x, A)` or declared
   * in a `Define` telescope.  Returns `A` such that `Γ ⊢ x : A`.
   *
   * Throws `EvalError` if `x` is not a typed variable in scope.
   */
  def lookupType(x: String, env: Environment): Type = {
    @tailrec
    def loop(
      ctx: Context, vals: List[Val], formulas: List[Formula],
      opaques: Nameless[Set[Ident]]
    ): Type = ctx match {
      case Context.Empty => throw EvalError(s"lookupType: not found $x")
      case Context.Update(y, parent) =>
        vals match {
          case v :: rest =>
            if (x == y) {
              v match {
                case VVar(_, a) => a
                case _          => throw EvalError(s"lookupType: $x is not a VVar")
              }
            } else loop(parent, rest, formulas, opaques)
          case Nil => throw EvalError(s"lookupType: env out of sync for $x")
        }
      case Context.Define(loc, decls, parent) =>
        Declarations.declTelescope(decls).find(_._1 == x) match {
          case Some((_, a)) => eval(a, Environment(ctx, vals, formulas, opaques))
          case None         => loop(parent, vals, formulas, opaques)
        }
      case Context.Substitute(_, parent) =>
        formulas match {
          case _ :: rest => loop(parent, vals, rest, opaques)
          case Nil       => throw EvalError(s"lookupType: env out of sync for $x (Substitute)")
        }
    }
    loop(env.ctx, env.vals, env.formulas, env.opaques)
  }

  def lookupFormula(i: Name, env: Environment): Formula = Environment.lookupName(i, env)

  /**
   * `Nominal` typeclass instances for the runtime structures.
   *
   * These instances define how dimension substitution `[i ↦ φ]` and name swapping
   * `(i j)` act on contexts, environments, and values.  They are used pervasively
   * by `Nominal.act`, `Nominal.face`, `Nominal.swap`, etc.
   */
  given nominalContext: Nominal[Context] with {
    def support(ctx: Context): List[Name] = Nil
    def act(ctx: Context, sub: (Name, Formula)): Context = ctx
    def swap(ctx: Context, names: (Name, Name)): Context = ctx
  }

  given nominalEnvironment: Nominal[Environment] with {
    def support(env: Environment): List[Name] = {
      Nominal.support[(Context, List[Val], List[Formula], Nameless[Set[Ident]])](
        (env.ctx, env.vals, env.formulas, env.opaques)
      )
    }
    def act(env: Environment, sub: (Name, Formula)): Environment = {
      val r = Nominal.act[(Context, List[Val], List[Formula], Nameless[Set[Ident]])](
        (env.ctx, env.vals, env.formulas, env.opaques), sub
      )
      Environment(r._1, r._2, r._3, r._4)
    }
    def swap(env: Environment, names: (Name, Name)): Environment = {
      val r = Nominal.swap[(Context, List[Val], List[Formula], Nameless[Set[Ident]])](
        (env.ctx, env.vals, env.formulas, env.opaques), names
      )
      Environment(r._1, r._2, r._3, r._4)
    }
  }

  given nominalSetIdent: Nominal[Set[Ident]] with {
    def support(identSet: Set[Ident]): List[Name] = Nil
    def act(identSet: Set[Ident], sub: (Name, Formula)): Set[Ident] = identSet
    def swap(identSet: Set[Ident], names: (Name, Name)): Set[Ident] = identSet
  }

  given nominalVal: Nominal[Val] with {
    def support(v: Val): List[Name] = v match {
      case VU                     => Nil
      case Closure(_, e)          => Nominal.support(e)
      case VPi(_, u, v)           => Nominal.support((u, v))
      case VComp(a, u, ts)        => Nominal.support((a, u, ts))
      case VPathP(a, v0, v1)      => Nominal.support((a, v0, v1))
      case VPLam(i, v)            => Nominal.support(v).filter(_ != i)
      case VSigma(u, v)           => Nominal.support((u, v))
      case VPair(u, v)            => Nominal.support((u, v))
      case VFst(u)                => Nominal.support(u)
      case VSnd(u)                => Nominal.support(u)
      case VCon(_, vs)            => Nominal.support(vs)
      case VPCon(_, a, vs, phis)  => Nominal.support((a, vs, phis))
      case VHComp(a, u, ts)       => Nominal.support((a, u, ts))
      case VVar(_, v)             => Nominal.support(v)
      case VOpaque(_, v)          => Nominal.support(v)
      case VApp(u, v)             => Nominal.support((u, v))
      case VLam(_, u, v)          => Nominal.support((u, v))
      case VAppFormula(u, phi)    => Nominal.support((u, phi))
      case VSplit(u, v)           => Nominal.support((u, v))
      case VGlue(a, ts)           => Nominal.support((a, ts))
      case VGlueElem(a, ts)       => Nominal.support((a, ts))
      case VUnGlueElem(a, ts)     => Nominal.support((a, ts))
      case VCompU(a, ts)          => Nominal.support((a, ts))
      case VUnGlueElemU(a, b, es) => Nominal.support((a, b, es))
      case VIdPair(u, us)         => Nominal.support((u, us))
      case VId(a, u, v)           => Nominal.support((a, u, v))
      case VIdJ(a, u, c, d, x, p) => Nominal.support((a, u, c, d, x, p))
      case VMeta(_) => Nil
    }

    def act(u: Val, iphi: (Name, Formula)): Val = {
      val (i, phi) = iphi
      if (!support(u).contains(i)) return u
      def acti[A: Nominal](value: A): A = Nominal.act(value, iphi)
      val phiSupport = Nominal.support(phi)
      u match {
        case VU              => VU
        case Closure(t, e)   => Closure(t, acti(e))
        case VPi(icity, a, f)    => VPi(icity, acti(a), acti(f))
        case VComp(a, v, ts) => compLine(acti(a), acti(v), acti(ts))
        case VPathP(a, u, v) => VPathP(acti(a), acti(u), acti(v))
        case VPLam(j, v) =>
          if (j == i) u
          else if (!phiSupport.contains(j)) VPLam(j, acti(v))
          else {
            val k = Nominal.fresh((v, Formula.Atom(i), phi))
            VPLam(k, acti(Nominal.swap(v, (j, k))))
          }
        case VSigma(a, f)             => VSigma(acti(a), acti(f))
        case VPair(u, v)              => VPair(acti(u), acti(v))
        case VFst(u)                  => fstVal(acti(u))
        case VSnd(u)                  => sndVal(acti(u))
        case VCon(c, vs)              => VCon(c, acti(vs))
        case VPCon(c, a, vs, phis)    => pcon(c, acti(a), acti(vs), acti(phis))
        case VHComp(a, u, us)         => hComp(acti(a), acti(u), acti(us))
        case VVar(x, v)               => VVar(x, acti(v))
        case VOpaque(x, v)            => VOpaque(x, acti(v))
        case VAppFormula(u, psi)      => appFormula(acti(u), acti(psi))
        case VApp(u, v)               => app(acti(u), acti(v))
        case VLam(x, t, u)            => VLam(x, acti(t), acti(u))
        case VSplit(u, v)             => app(acti(u), acti(v))
        case VGlue(a, ts)             => glue(acti(a), acti(ts))
        case VGlueElem(a, ts)         => glueElem(acti(a), acti(ts))
        case VUnGlueElem(a, ts)       => unglueElem(acti(a), acti(ts))
        case VUnGlueElemU(a, b, es)   => unGlueU(acti(a), acti(b), acti(es))
        case VCompU(a, ts)            => compUniv(acti(a), acti(ts))
        case VIdPair(u, us)           => VIdPair(acti(u), acti(us))
        case VId(a, u, v)             => VId(acti(a), acti(u), acti(v))
        case VIdJ(a, u, c, d, x, p)   =>
          idJ(acti(a), acti(u), acti(c), acti(d), acti(x), acti(p))
        case VMeta(_) => u
      }
    }

    def swap(u: Val, ij: (Name, Name)): Val = {
      def sw[A: Nominal](value: A): A = Nominal.swap(value, ij)
      u match {
        case VU                       => VU
        case Closure(t, e)            => Closure(t, sw(e))
        case VPi(icity, a, f)         => VPi(icity, sw(a), sw(f))
        case VComp(a, v, ts)          => VComp(sw(a), sw(v), sw(ts))
        case VPathP(a, u, v)          => VPathP(sw(a), sw(u), sw(v))
        case VPLam(k, v)              => VPLam(Name.swapName(k, ij._1, ij._2), sw(v))
        case VSigma(a, f)             => VSigma(sw(a), sw(f))
        case VPair(u, v)              => VPair(sw(u), sw(v))
        case VFst(u)                  => VFst(sw(u))
        case VSnd(u)                  => VSnd(sw(u))
        case VCon(c, vs)              => VCon(c, sw(vs))
        case VPCon(c, a, vs, phis)    => VPCon(c, sw(a), sw(vs), sw(phis))
        case VHComp(a, u, us)         => VHComp(sw(a), sw(u), sw(us))
        case VVar(x, v)               => VVar(x, sw(v))
        case VOpaque(x, v)            => VOpaque(x, sw(v))
        case VAppFormula(u, psi)      => VAppFormula(sw(u), sw(psi))
        case VApp(u, v)               => VApp(sw(u), sw(v))
        case VLam(x, u, v)            => VLam(x, sw(u), sw(v))
        case VSplit(u, v)             => VSplit(sw(u), sw(v))
        case VGlue(a, ts)             => VGlue(sw(a), sw(ts))
        case VGlueElem(a, ts)         => VGlueElem(sw(a), sw(ts))
        case VUnGlueElem(a, ts)       => VUnGlueElem(sw(a), sw(ts))
        case VUnGlueElemU(a, b, es)   => VUnGlueElemU(sw(a), sw(b), sw(es))
        case VCompU(a, ts)            => VCompU(sw(a), sw(ts))
        case VIdPair(u, us)           => VIdPair(sw(u), sw(us))
        case VId(a, u, v)             => VId(sw(a), sw(u), sw(v))
        case VIdJ(a, u, c, d, x, p)   =>
          VIdJ(sw(a), sw(u), sw(c), sw(d), sw(x), sw(p))
        case VMeta(_) => u
      }
    }
  }

  /**
   * Evaluate a term `t` in environment `ρ` to a value.
   *
   * {{{
   *   ρ ⊢ t ↓ v    (evaluate `t` under `ρ` to value `v`)
   * }}}
   *
   * Terms that are already values (lambdas, splits, sums) become `Closure`s
   * pairing the term with its environment.  Eliminators reduce on-the-fly
   * (β-reduction, path application, composition).
   */
  def eval(t: Term, env: Environment): Val = {
    val opaqueSet = env.opaques.value
    t match {
      case Term.U => VU
      case Term.App(_, r, s) => app(eval(r, env), eval(s, env))
      case Term.Var(x) =>
        if (opaqueSet.contains(x)) VOpaque(x, lookupType(x, env))
        else lookupVal(x, env)
      case Term.Pi(icity, lam @ Term.Lam(_, _, a, _)) => VPi(icity, eval(a, env), Closure(lam, env))
      case Term.Sigma(lam @ Term.Lam(_, _, a, _)) => VSigma(eval(a, env), Closure(lam, env))
      case Term.Pair(a, b) => VPair(eval(a, env), eval(b, env))
      case Term.Fst(a) => fstVal(eval(a, env))
      case Term.Snd(a) => sndVal(eval(a, env))
      case Term.Where(t, decls) => eval(t, Environment.addDeclWhere(decls, env))
      case Term.Con(name, ts) => VCon(name, ts.map(eval(_, env)))
      case Term.PCon(name, a, ts, phis) =>
        pcon(name, eval(a, env), ts.map(eval(_, env)), phis.map(evalFormula(env, _)))
      case t @ Term.Lam(_, _, _, _)       => Closure(t, env)
      case t @ Term.Split(_, _, _, _)   => Closure(t, env)
      case t @ Term.Sum(_, _, _)        => Closure(t, env)
      case t @ Term.HSum(_, _, _)       => Closure(t, env)
      case t @ Term.Undef(_, _)         => Closure(t, env)
      case t @ Term.Hole(_)             => Closure(t, env)
      case Term.PathP(a, e0, e1) => VPathP(eval(a, env), eval(e0, env), eval(e1, env))
      case Term.PLam(i, t) =>
        val j = Nominal.fresh(env)
        VPLam(j, eval(t, Environment.substitute((i, Formula.Atom(j)), env)))
      case Term.AppFormula(e, phi) => appFormula(eval(e, env), evalFormula(env, phi))
      case Term.Comp(a, t0, ts) =>
        compLine(eval(a, env), eval(t0, env), evalSystem(env, ts))
      case Term.HComp(a, t0, ts) =>
        hComp(eval(a, env), eval(t0, env), evalSystem(env, ts))
      case Term.Fill(a, t0, ts) =>
        fillLine(eval(a, env), eval(t0, env), evalSystem(env, ts))
      case Term.Glue(a, ts) => glue(eval(a, env), evalSystem(env, ts))
      case Term.GlueElem(a, ts) => glueElem(eval(a, env), evalSystem(env, ts))
      case Term.UnGlueElem(a, ts) => unglueElem(eval(a, env), evalSystem(env, ts))
      case Term.Id(a, r, s) => VId(eval(a, env), eval(r, env), eval(s, env))
      case Term.IdPair(b, ts) => VIdPair(eval(b, env), evalSystem(env, ts))
      case Term.IdJ(a, t, c, d, x, p) =>
        idJ(eval(a, env), eval(t, env), eval(c, env),
            eval(d, env), eval(x, env), eval(p, env))
      case Term.Meta(_) => throw EvalError("Cannot evaluate unsolved meta")
      case _ => throw EvalError(s"Cannot evaluate $t")
    }
  }

  def evals(env: Environment, bindings: List[(Ident, Term)]): List[(Ident, Val)] = {
    bindings.map { case (b, t) => (b, eval(t, env)) }
  }

  def evalFormula(env: Environment, phi: Formula): Formula = phi match {
    case Formula.Atom(i)    => lookupFormula(i, env)
    case Formula.NegAtom(i) => Formula.negFormula(lookupFormula(i, env))
    case Formula.And(p, q)  => Formula.andFormula(evalFormula(env, p), evalFormula(env, q))
    case Formula.Or(p, q)   => Formula.orFormula(evalFormula(env, p), evalFormula(env, q))
    case _                  => phi
  }

  def evalSystem(env: Environment, ts: System[Term]): System[Val] = {
    val systemAsList = ts.toList.flatMap { case (alpha, talpha) =>
      val betas = Face.meetss(
        alpha.toList.map { case (i, d) =>
          Formula.invFormula(lookupFormula(i, env), d)
        }
      )
      betas.map { beta =>
        (beta, eval(talpha, Nominal.face(env, beta)))
      }
    }
    SystemOps.mkSystem(systemAsList)
  }

  /**
   * Apply a value `u` (a function or split) to an argument `v`.
   *
   * {{{
   *   ─────────────────────────────────────── (β-Lam)
   *   (λ x. t)[ρ] v  =  t[ρ, x ↦ v]
   *
   *   Γ ⊢ u : Π(x:A).B    Γ ⊢ v : A
   *   ─────────────────────────────── (App)
   *   Γ ⊢ u v : B[x ↦ v]
   * }}}
   *
   * Also handles case splitting on `VCon`/`VPCon`, composition under `VHComp`
   * (for split), and function application under `VComp(VPLam(i, VPi(A, B)))`.
   * Returns `VApp(u, v)` when `u` is neutral (stuck).
   */
  def app(u: Val, v: Val): Val = (u, v) match {
    case (Closure(Term.Lam(_, x, _, t), e), _) =>
      eval(t, Environment.update((x, v), e))
    case (Closure(Term.Split(_, _, _, branches), e), VCon(c, vs)) =>
      Branch.lookupBranch(c, branches) match {
        case Some(OrdinaryBranch(_, xs, t)) =>
          eval(t, Environment.updateAll(xs.zip(vs), e))
        case _ => throw EvalError(s"app: missing case in split for $c")
      }
    case (Closure(Term.Split(_, _, _, branches), e), VPCon(c, _, us, phis)) =>
      Branch.lookupBranch(c, branches) match {
        case Some(PathBranch(_, xs, is, t)) =>
          eval(t, Environment.substituteAll(is.zip(phis), Environment.updateAll(xs.zip(us), e)))
        case _ => throw EvalError(s"app: missing case in split for $c")
      }
    case (Closure(Term.Split(_, _, ty, _), e), VHComp(a, w, ws)) =>
      eval(ty, e) match {
        case VPi(_, _, f) =>
          val j = Nominal.fresh((e, v))
          val systemAtJ = ws.map { case (alpha, uAlpha) => alpha -> appFormula(uAlpha, Formula.Atom(j)) }
          val appliedValue = app(u, w)
          val appliedSystem = systemAtJ.map { case (alpha, wAlpha) =>
            alpha -> app(Nominal.face(u, alpha), wAlpha)
          }
          comp(j, app(f, fill(j, a, w, systemAtJ)), appliedValue, appliedSystem)
        case _ => throw EvalError(s"app: Split annotation not a Pi type $u")
      }
    case (Closure(Term.Split(_, _, _, _), _), _) if Val.isNeutral(v) => VSplit(u, v)
    case (VComp(VPLam(i, VPi(_, a, f)), li0, ts), vi1) =>
      val j = Nominal.fresh((u, vi1))
      val (aj, fj) = (Nominal.swap(a, (i, j)), Nominal.swap(f, (i, j)))
      val sysAtJ = ts.map { case (alpha, tAlpha) => alpha -> appFormula(tAlpha, Formula.Atom(j)) }
      val transFillNegResult = transFillNeg(j, aj, vi1)
      val transNegResult = transNeg(j, aj, vi1)
      comp(j, app(fj, transFillNegResult), app(li0, transNegResult),
        sysAtJ.map { case (alpha, tAlpha) => alpha -> app(tAlpha, Nominal.face(transFillNegResult, alpha)) })
    case _ if Val.isNeutral(u) => VApp(u, v)
    case _ => throw EvalError(s"app\n  $u\n  $v")
  }

  def fstVal(v: Val): Val = v match {
    case VPair(a, _) => a
    case u if Val.isNeutral(u) => VFst(u)
    case u => throw EvalError(s"fstVal: $u is not neutral.")
  }

  def sndVal(v: Val): Val = v match {
    case VPair(_, b) => b
    case u if Val.isNeutral(u) => VSnd(u)
    case u => throw EvalError(s"sndVal: $u is not neutral.")
  }

  /**
   * Infer the type of a neutral value `v`.
   *
   * Selected typing rules (read: premises above the line, conclusion below):
   *
   * {{{
   *   Γ ⊢ x : A                Γ ⊢ t : Σ(x:A).B
   *   ─────────────── (Var)    ─────────────────── (Fst)
   *   Γ ⊢ x : A               Γ ⊢ fst t : A
   *
   *   Γ ⊢ t : Σ(x:A).B            Γ ⊢ t₀ : Π(x:A).B    Γ ⊢ t₁ : A
   *   ───────────────────── (Snd)  ────────────────────────────────── (App)
   *   Γ ⊢ snd t : B(fst t)        Γ ⊢ t₀ t₁ : B t₁
   *
   *   Γ ⊢ t : PathP A a₀ a₁    φ : 𝕀
   *   ──────────────────────────────── (AppFormula)
   *   Γ ⊢ t @@ φ : A φ
   *
   *   Γ, i:𝕀 ⊢ A : U    Γ ⊢ u : A 0    Γ, i:𝕀 ⊢ [φ ↦ t] : A[φ]
   *   ─────────────────────────────────────────────────────────── (Comp)
   *   Γ ⊢ comp i A [φ ↦ t] u : A 1
   * }}}
   */
  def inferType(v: Val): Type = v match {
    case VVar(_, t)     => t
    case VOpaque(_, t)  => t
    case Closure(Term.Undef(_, t), env) => eval(t, env)
    case VFst(t) => inferType(t) match {
      case VSigma(a, _) => a
      case ty => throw EvalError(s"inferType: expected Sigma type for $v, got $ty")
    }
    case VSnd(t) => inferType(t) match {
      case VSigma(_, f) => app(f, VFst(t))
      case ty => throw EvalError(s"inferType: expected Sigma type for $v, got $ty")
    }
    case VSplit(s @ Closure(Term.Split(_, _, t, _), env), v1) => eval(t, env) match {
      case VPi(_, _, f) => app(f, v1)
      case ty => throw EvalError(s"inferType: Pi type expected for split in $v, got $ty")
    }
    case VApp(t0, t1) => inferType(t0) match {
      case VPi(_, _, f) => app(f, t1)
      case ty => throw EvalError(s"inferType: expected Pi type for $v, got $ty")
    }
    case VAppFormula(t, phi) => inferType(t) match {
      case VPathP(a, _, _) => appFormula(a, phi)
      case ty => throw EvalError(s"inferType: expected PathP type for $v, got $ty")
    }
    case VComp(a, _, _) => appFormula(a, Formula.Dir(Dir.One))
    case VUnGlueElemU(_, b, _) => b
    case VIdJ(_, _, c, _, x, p) => app(app(c, x), p)
    case _ => throw EvalError(s"inferType: not neutral $v")
  }

  /**
   * Apply a path `v` to a dimension formula `φ`  (`v @@ φ`).
   *
   * {{{
   *   Γ, i:𝕀 ⊢ u : A i
   *   ─────────────────────────────────── (PathP-β)
   *   Γ ⊢ (λ̂ i. u) @@ φ = u[i ↦ φ] : A φ
   *
   *   Γ ⊢ p : PathP A a₀ a₁
   *   ──────────────────────── (PathP-0)   ──────────────────────── (PathP-1)
   *   Γ ⊢ p @@ 0 = a₀ : A 0               Γ ⊢ p @@ 1 = a₁ : A 1
   * }}}
   *
   * When `v` is neutral and `φ` is not a direction endpoint, returns `VAppFormula(v, φ)`.
   */
  def appFormula(v: Val, phi: Formula): Val = (v, phi) match {
    case (VPLam(i, u), _)                  => Nominal.act(u, (i, phi))
    case (t @ Closure(Term.Hole(_), _), _) => VAppFormula(t, phi)
    case _ if Val.isNeutral(v) =>
      (inferType(v), phi) match {
        case (VPathP(_, a0, _), Formula.Dir(Dir.Zero)) => a0
        case (VPathP(_, _, a1), Formula.Dir(Dir.One))  => a1
        case _ => VAppFormula(v, phi)
      }
    case _ => throw EvalError(s"(@@): $v should be neutral.")
  }

  def appFormulaName(v: Val, j: Name): Val = v match {
    case VPLam(i, u) => Nominal.swap(u, (i, j))
    case _           => VAppFormula(v, Formula.Atom(j))
  }

  /**
   * Kan composition and filling.
   *
   * {{{
   *   Γ, i:𝕀 ⊢ A : U    Γ ⊢ u₀ : A 0
   *   Γ, i:𝕀 ⊢ [φ ↦ u] : A[φ]    u(i=0) = u₀[φ]
   *   ──────────────────────────────────────────── (comp)
   *   Γ ⊢ comp i A [φ ↦ u] u₀ : A 1
   *
   *   Γ, i:𝕀 ⊢ A : U    Γ ⊢ u₀ : A 0    Γ, i:𝕀 ⊢ [φ ↦ u] : A[φ]
   *   ────────────────────────────────────────────────────────────── (fill)
   *   Γ ⊢ fill i A [φ ↦ u] u₀ : Path (A) u₀ (comp i A [φ ↦ u] u₀)
   * }}}
   *
   * The type line `A` is given as `ty = A i` (the fibre at the current dimension).
   * Dispatches on the shape of `A i` to use the respective composition algorithm
   * for `Π`, `Σ`, `PathP`, `Id`, inductive types, Glue, and the universe;
   * for everything else a `VComp` neutral is returned.
   */
  def comp(i: Name, ty: Type, u: Val, faceVals: System[Val]): Val = {
    if (faceVals.contains(Face.eps)) {
      Nominal.face(faceVals(Face.eps), Face.dir(i, Dir.One))
    } else ty match {
      case VPathP(p, v0, v1) =>
        val j = Nominal.fresh((Formula.Atom(i), ty, u, faceVals))
        VPLam(j, comp(i, appFormula(p, Formula.Atom(j)), appFormula(u, Formula.Atom(j)),
          SystemOps.insertsSystem(List((Face.dir(j, Dir.Zero), v0), (Face.dir(j, Dir.One), v1)),
            faceVals.map { case (alpha, tAlpha) => alpha -> appFormula(tAlpha, Formula.Atom(j)) })))
      case VId(b, v0, v1) => u match {
        case VIdPair(r, _) if faceVals.values.forall(isIdPair) =>
          val j = Nominal.fresh((Formula.Atom(i), ty, u, faceVals))
          val w = VPLam(j, comp(i, b, appFormula(r, Formula.Atom(j)),
            SystemOps.insertsSystem(
              List((Face.dir(j, Dir.Zero), v0),
                   (Face.dir(j, Dir.One), v1)),
              faceVals.map { case (alpha, tAlpha) => alpha -> appFormulaIdPair(tAlpha, j) })))
          val tsFaced = Nominal.face(faceVals, Face.dir(i, Dir.One))
          VIdPair(w, SystemOps.joinSystem(
            tsFaced.map { case (alpha, tAlpha) =>
              alpha -> sysOfIdPair(tAlpha)
            }))
        case _ => VComp(VPLam(i, ty), u, faceVals.map { case (alpha, tAlpha) => alpha -> VPLam(i, tAlpha) })
      }
      case VSigma(sa, f) =>
        val firstComponentSystems  = faceVals.map { case (alpha, tAlpha) => alpha -> fstVal(tAlpha) }
        val secondComponentSystems = faceVals.map { case (alpha, tAlpha) => alpha -> sndVal(tAlpha) }
        val (firstComponent, secondComponent) = (fstVal(u), sndVal(u))
        val filledFirstComponent  = fill(i, sa, firstComponent, firstComponentSystems)
        val composedFirstComponent  = comp(i, sa, firstComponent, firstComponentSystems)
        val composedSecondComponent = comp(i, app(f, filledFirstComponent), secondComponent, secondComponentSystems)
        VPair(composedFirstComponent, composedSecondComponent)
      case VPi(_, _, _) =>
        VComp(VPLam(i, ty), u, faceVals.map { case (alpha, tAlpha) => alpha -> VPLam(i, tAlpha) })
      case VU =>
        compUniv(u, faceVals.map { case (alpha, tAlpha) => alpha -> VPLam(i, tAlpha) })
      case VCompU(ca, es) if !isNeutralU(i, es, u, faceVals) =>
        compU(i, ca, es, u, faceVals)
      case VGlue(baseType, equivs) if !isNeutralGlue(i, equivs, u, faceVals) =>
        compGlue(i, baseType, equivs, u, faceVals)
      case Closure(Term.Sum(_, _, sumLabels), env) => u match {
        case VCon(n, us) if faceVals.values.forall { case VCon(_, _) => true; case _ => false } =>
          Label.lookupLabel(n, sumLabels) match {
            case Some(as) =>
              val systemsWithBases = SystemOps.transposeSystemAndList(
                faceVals.map { case (alpha, tAlpha) => alpha -> Val.unCon(tAlpha) }, us)
              VCon(n, comps(i, as, env, systemsWithBases))
            case None => throw EvalError(s"comp: missing constructor in labelled sum $n")
          }
        case _ => VComp(VPLam(i, ty), u, faceVals.map { case (alpha, tAlpha) => alpha -> VPLam(i, tAlpha) })
      }
      case Closure(Term.HSum(_, _, _), _) => compHIT(i, ty, u, faceVals)
      case _ => VComp(VPLam(i, ty), u, faceVals.map { case (alpha, tAlpha) => alpha -> VPLam(i, tAlpha) })
    }
  }

  def compNeg(i: Name, ty: Type, u: Val, faceVals: System[Val]): Val = {
    comp(i, Nominal.sym(ty, i), u, Nominal.sym(faceVals, i))
  }

  def compLine(ty: Type, u: Val, faceVals: System[Val]): Val = {
    val i = Nominal.fresh((ty, u, faceVals))
    comp(i, appFormula(ty, Formula.Atom(i)), u,
      faceVals.map { case (alpha, tAlpha) => alpha -> appFormula(tAlpha, Formula.Atom(i)) })
  }

  def compConstLine(ty: Type, u: Val, faceVals: System[Val]): Val = {
    val i = Nominal.fresh((ty, u, faceVals))
    comp(i, ty, u, faceVals.map {
      case (alpha, tAlpha) => alpha -> appFormula(tAlpha, Formula.Atom(i))
    })
  }

  def comps(i: Name, typedIdents: List[(Ident, Term)], env: Environment, systemsWithBases: List[(System[Val], Val)]): List[Val] = {
    (typedIdents, systemsWithBases) match {
      case (Nil, Nil) => Nil
      case ((x, a) :: typeRest, (ts, u) :: typeValPairRest) =>
        val filledValue = fill(i, eval(a, env), u, ts)
        val composedValue = comp(i, eval(a, env), u, ts)
        val composedValues = comps(i, typeRest, Environment.update((x, filledValue), env), typeValPairRest)
        composedValue :: composedValues
      case _ => throw EvalError("comps: different lengths of types and values")
    }
  }

  def fill(i: Name, ty: Type, u: Val, faceVals: System[Val]): Val = {
    val j = Nominal.fresh((Formula.Atom(i), ty, u, faceVals))
    comp(j, Nominal.conj(ty, (i, j)), u,
      SystemOps.insertSystem(Face.dir(i, Dir.Zero), u, Nominal.conj(faceVals, (i, j))))
  }

  def fillNeg(i: Name, ty: Type, u: Val, faceVals: System[Val]): Val = {
    Nominal.sym(fill(i, Nominal.sym(ty, i), u, Nominal.sym(faceVals, i)), i)
  }

  def fillLine(ty: Type, u: Val, faceVals: System[Val]): Val = {
    val i = Nominal.fresh((ty, u, faceVals))
    VPLam(i, fill(i, appFormula(ty, Formula.Atom(i)), u,
      faceVals.map { case (alpha, tAlpha) => alpha -> appFormula(tAlpha, Formula.Atom(i)) }))
  }

  /**
   * Transport and filling along a type line.
   *
   * {{{
   *   Γ, i:𝕀 ⊢ A : U    Γ ⊢ u₀ : A 0
   *   ─────────────────────────────────── (trans)
   *   Γ ⊢ trans i A u₀ : A 1
   * }}}
   *
   * `trans i A u₀`  is  `comp i A [] u₀`  — composition with an empty system.
   *
   * `fill i A u₀`  is  the path `λ̂ j. comp j (A ∧ j) [i=0 ↦ u₀] u₀`
   * witnessing that `u₀` and its transport are connected inside `A`.
   */
  def trans(i: Name, v0: Val, v1: Val): Val = comp(i, v0, v1, Map.empty)

  def transNeg(i: Name, ty: Type, u: Val): Val = trans(i, Nominal.sym(ty, i), u)

  def transLine(u: Val, v: Val): Val = {
    val i = Nominal.fresh((u, v))
    trans(i, appFormula(u, Formula.Atom(i)), v)
  }

  def transNegLine(u: Val, v: Val): Val = {
    val i = Nominal.fresh((u, v))
    transNeg(i, appFormula(u, Formula.Atom(i)), v)
  }

  def transps(i: Name, typedIdents: List[(Ident, Term)], env: Environment, baseVals: List[Val]): List[Val] = {
    (typedIdents, baseVals) match {
      case (Nil, Nil) => Nil
      case ((x, a) :: typeRest, u :: valRest) =>
        val filledValue = transFill(i, eval(a, env), u)
        val transportedValue = trans(i, eval(a, env), u)
        val transportedValues = transps(i, typeRest, Environment.update((x, filledValue), env), valRest)
        transportedValue :: transportedValues
      case _ => throw EvalError("transps: different lengths")
    }
  }

  def transFill(i: Name, ty: Type, u: Val): Val = fill(i, ty, u, Map.empty)

  def transFillNeg(i: Name, ty: Type, u: Val): Val = {
    Nominal.sym(transFill(i, Nominal.sym(ty, i), u), i)
  }

  def squeeze(i: Name, ty: Type, u: Val): Val = {
    val j = Nominal.fresh((Formula.Atom(i), ty, u))
    val ui1 = Nominal.face(u, Face.dir(i, Dir.One))
    comp(j, Nominal.disj(ty, (i, j)), u,
      SystemOps.mkSystem(List((Face.dir(i, Dir.One), ui1))))
  }

  def squeezes(i: Name, typedIdents: List[(Ident, Term)], env: Environment, baseVals: List[Val]): List[Val] = {
    val j = Nominal.fresh((baseVals, env, Formula.Atom(i)))
    val squeezedSystemsAndValues = baseVals.map { u =>
      (SystemOps.mkSystem(List(
        (Face.dir(i, Dir.One), Nominal.face(u, Face.dir(i, Dir.One)))
      )), u)
    }
    comps(j, typedIdents, Nominal.disj(env, (i, j)), squeezedSystemsAndValues)
  }

  /**
   * The identity eliminator `idJ`.
   *
   * {{{
   *   Γ ⊢ A : U    Γ ⊢ a : A
   *   Γ ⊢ C : (x : A) → Id A a x → U
   *   Γ ⊢ d : C a (reflId a)
   *   Γ ⊢ x : A    Γ ⊢ p : Id A a x
   *   ──────────────────────────────── (IdJ / J)
   *   Γ ⊢ idJ A a C d x p : C x p
   * }}}
   *
   * When `p = VIdPair(w, ws)` the J-rule fires and reduces to a composition;
   * otherwise it suspends as `VIdJ(A, a, C, d, x, p)`.
   */
  def idJ(a: Val, v: Val, c: Val, d: Val, x: Val, p: Val): Val = p match {
    case VIdPair(w, ws) =>
      val names = Nominal.freshs((a, v, c, d, x, p))
      val i = names(0)
      val j = names(1)
      val w2 = VIdPair(
        VPLam(j, appFormula(w, Formula.andFormula(Formula.Atom(i), Formula.Atom(j)))),
        SystemOps.insertSystem(Face.dir(i, Dir.Zero), v, ws))
      comp(i, app(app(c, appFormula(w, Formula.Atom(i))), w2), d,
        Nominal.border(d, shape(ws)))
    case _ => VIdJ(a, v, c, d, x, p)
  }

  def isIdPair(v: Val): Boolean = v match {
    case VIdPair(_, _) => true
    case _             => false
  }

  private def appFormulaIdPair(v: Val, j: Name): Val = v match {
    case VIdPair(z, _) => appFormula(z, Formula.Atom(j))
    case _             => appFormula(v, Formula.Atom(j))
  }

  private def sysOfIdPair(v: Val): System[Val] = v match {
    case VIdPair(_, ws) => ws
    case _              => Map.empty
  }

  def shape(ws: System[Val]): System[Unit] = {
    ws.map { case (f, _) => f -> () }
  }

  /**
   * Higher inductive types (HITs): constructors and composition.
   *
   * `pcon c A us phis` builds a path-constructor application, reducing to a
   * concrete value when the associated face system is total.
   *
   * `compHIT i A u [φ ↦ ts]` computes composition in a HIT by factoring through
   * transport (`transpHIT`) and homogeneous composition (`hComp`).
   *
   * `transpHIT i A u` transports `u : A 0` to `A 1` along a line `A : 𝕀 → HSum`.
   *
   * `squeezeHIT i A u` computes a "squeeze" (diagonal composition) in a HIT,
   * used as a subroutine in `compHIT`.
   */
  def pcon(c: LabelIdent, a: Val, us: List[Val], phis: List[Formula]): Val = a match {
    case Closure(Term.HSum(_, _, lbls), env) =>
      Label.lookupPathLabel(c, lbls) match {
        case Some((tele, is, ts)) =>
          val env2 = Environment.substituteAll(is.zip(phis), Environment.updateTelescope(tele, us, env))
          val evaluatedSystem = evalSystem(env2, ts)
          if (evaluatedSystem.contains(Face.eps)) evaluatedSystem(Face.eps)
          else VPCon(c, a, us, phis)
        case None => throw EvalError("pcon: label not found")
      }
    case _ => VPCon(c, a, us, phis)
  }

  def compHIT(i: Name, sumType: Type, u: Val, faceVals: System[Val]): Val = {
    if (Val.isNeutral(u) || Val.isNeutralSystem(faceVals)) {
      VComp(VPLam(i, sumType), u, faceVals.map { case (alpha, uAlpha) => alpha -> VPLam(i, uAlpha) })
    } else {
      hComp(
        Nominal.face(sumType, Face.dir(i, Dir.One)),
        transpHIT(i, sumType, u),
        faceVals.map { case (alpha, uAlpha) =>
          alpha -> VPLam(i, squeezeHIT(i, Nominal.face(sumType, alpha), uAlpha))
        })
    }
  }

  def transpHIT(i: Name, sumType: Type, u: Val): Val = sumType match {
    case Closure(Term.HSum(_, _, sumLabels), env) =>
      u match {
        case VCon(n, us) =>
          Label.lookupLabel(n, sumLabels) match {
            case Some(as) => VCon(n, transps(i, as, env, us))
            case None => throw EvalError(s"transpHIT: missing constructor $n")
          }
        case VPCon(c, _, ws0, phis) =>
          Label.lookupLabel(c, sumLabels) match {
            case Some(as) =>
              pcon(c, Nominal.face(sumType, Face.dir(i, Dir.One)),
                transps(i, as, env, ws0), phis)
            case None => throw EvalError(s"transpHIT: missing path constructor $c")
          }
        case VHComp(_, v, vs) =>
          val j = Nominal.fresh((sumType, u))
          val aij = Nominal.swap(sumType, (i, j))
          hComp(
            Nominal.face(sumType, Face.dir(i, Dir.One)),
            transpHIT(i, sumType, v),
            vs.map { case (alpha, vAlpha) =>
              alpha -> VPLam(j, transpHIT(j, Nominal.face(aij, alpha), appFormula(vAlpha, Formula.Atom(j))))
            })
        case _ => throw EvalError(s"transpHIT: neutral $u")
      }
    case _ => throw EvalError(s"transpHIT: not an HSum $sumType")
  }

  def squeezeHIT(i: Name, sumType: Type, u: Val): Val = sumType match {
    case Closure(Term.HSum(_, _, sumLabels), env) =>
      u match {
        case VCon(n, us) =>
          Label.lookupLabel(n, sumLabels) match {
            case Some(as) => VCon(n, squeezes(i, as, env, us))
            case None => throw EvalError(s"squeezeHIT: missing constructor $n")
          }
        case VPCon(c, _, ws0, phis) =>
          Label.lookupLabel(c, sumLabels) match {
            case Some(as) =>
              pcon(c, Nominal.face(sumType, Face.dir(i, Dir.One)),
                squeezes(i, as, env, ws0), phis)
            case None => throw EvalError(s"squeezeHIT: missing path constructor $c")
          }
        case VHComp(_, v, vs) =>
          val j = Nominal.fresh((sumType, u))
          hComp(
            Nominal.face(sumType, Face.dir(i, Dir.One)),
            squeezeHIT(i, sumType, v),
            vs.map { case (alpha, vAlpha) =>
              alpha.get(i) match {
                case None =>
                  alpha -> VPLam(j, squeezeHIT(i, Nominal.face(sumType, alpha), appFormula(vAlpha, Formula.Atom(j))))
                case Some(Dir.Zero) =>
                  alpha -> VPLam(j, transpHIT(i, Nominal.face(sumType, alpha.removed(i)), appFormula(vAlpha, Formula.Atom(j))))
                case Some(Dir.One) =>
                  alpha -> vAlpha
              }
            })
        case _ => throw EvalError(s"squeezeHIT: neutral $u")
      }
    case _ => throw EvalError(s"squeezeHIT: not an HSum $sumType")
  }

  def hComp(ty: Type, u: Val, faceVals: System[Val]): Val = {
    if (faceVals.contains(Face.eps)) appFormula(faceVals(Face.eps), Formula.Dir(Dir.One))
    else VHComp(ty, u, faceVals)
  }

  /**
   * Glue types and their elements.
   *
   * `Glue A [φ ↦ (T, e)]` — a type that is `A` outside `φ` and equivalent to `T`
   * on `φ`, witnessed by an equivalence `e : T ≃ A`.
   *
   * `glueElem v [φ ↦ u]` — an element of the Glue type with base part `v : A` and
   * component `u : T` on `φ`, subject to `e u = v [ φ ]`.
   *
   * `unglueElem`/`unGlue` — extract the base-type component from a glued element.
   *
   * `compGlue` — composition in a Glue type, following the Glue composition
   * algorithm of the cubical TT paper (§ Glue).
   */
  def equivDom(v: Val): Type = fstVal(v)
  def equivFun(v: Val): Val = fstVal(sndVal(v))
  def equivContr(v: Val): Val = sndVal(sndVal(v))

  def glue(baseType: Type, faceVals: System[Val]): Val = {
    if (faceVals.contains(Face.eps)) equivDom(faceVals(Face.eps))
    else VGlue(baseType, faceVals)
  }

  def glueElem(v: Val, us: System[Val]): Val = {
    if (us.contains(Face.eps)) us(Face.eps)
    else VGlueElem(v, us)
  }

  def unglueElem(w: Val, isos: System[Val]): Val = {
    if (isos.contains(Face.eps)) app(equivFun(isos(Face.eps)), w)
    else w match {
      case VGlueElem(v, _) => v
      case _ => VUnGlueElem(w, isos)
    }
  }

  def unGlue(w: Val, baseType: Type, equivs: System[Val]): Val = {
    if (equivs.contains(Face.eps)) app(equivFun(equivs(Face.eps)), w)
    else w match {
      case VGlueElem(v, _) => v
      case _ => throw EvalError(s"unGlue: neutral $w")
    }
  }

  def isNeutralGlue(i: Name, equivs: System[Val], baseVal: Val, faceVals: System[Val]): Boolean = {
    val equivsi0 = Nominal.face(equivs, Face.dir(i, Dir.Zero))
    ((!equivsi0.contains(Face.eps)) && Val.isNeutral(baseVal)) ||
    faceVals.exists { case (alpha, talpha) =>
      (!Nominal.face(equivs, alpha).contains(Face.eps)) && Val.isNeutral(talpha)
    }
  }

  def isNeutralU(i: Name, equivs: System[Val], baseVal: Val, faceVals: System[Val]): Boolean = {
    val eqsi0 = Nominal.face(equivs, Face.dir(i, Dir.Zero))
    ((!eqsi0.contains(Face.eps)) && Val.isNeutral(baseVal)) ||
    faceVals.exists { case (alpha, talpha) =>
      (!Nominal.face(equivs, alpha).contains(Face.eps)) && Val.isNeutral(talpha)
    }
  }

  def extend(baseType: Type, equivPair: Val, fiberSections: System[Val]): Val = {
    val i = Nominal.fresh((baseType, equivPair, fiberSections))
    val ts2 = fiberSections.map { case (alpha, tAlpha) =>
      alpha -> appFormula(app(Nominal.face(sndVal(equivPair), alpha), tAlpha), Formula.Atom(i))
    }
    comp(i, baseType, fstVal(equivPair), ts2)
  }

  def compGlue(i: Name, baseType: Type, equivs: System[Val], baseAtI0: Val, faceVals: System[Val]): Val = {
    val ai1 = Nominal.face(baseType, Face.dir(i, Dir.One))
    val ungluedValuesSystem = faceVals.map { case (alpha, wAlpha) =>
      alpha -> unGlue(wAlpha, Nominal.face(baseType, alpha), Nominal.face(equivs, alpha))
    }
    val ungluedValuesAtI1 = Nominal.face(ungluedValuesSystem, Face.dir(i, Dir.One))
    val ungluedValueAtI0 = unGlue(baseAtI0, Nominal.face(baseType, Face.dir(i, Dir.Zero)),
      Nominal.face(equivs, Face.dir(i, Dir.Zero)))
    val composedValueAtI1Preliminary = comp(i, baseType, ungluedValueAtI0, ungluedValuesSystem)
    val equivalencesAtI1 = Nominal.face(equivs, Face.dir(i, Dir.One))
    val equivalencesWithoutI = equivs.filter { case (alpha, _) => !alpha.contains(i) }

    val filledValuesForEquivalences = equivalencesWithoutI.map { case (gamma, equivG) =>
      gamma -> fill(i, equivDom(equivG), Nominal.face(baseAtI0, gamma), Nominal.face(faceVals, gamma))
    }
    val composedValuesForEquivalencesAtI1 = equivalencesWithoutI.map { case (gamma, equivG) =>
      gamma -> comp(i, equivDom(equivG), Nominal.face(baseAtI0, gamma), Nominal.face(faceVals, gamma))
    }

    val pathComposedForEquivalences = equivalencesWithoutI.map { case (gamma, equivG) =>
      gamma -> pathComp(i, Nominal.face(baseType, gamma), Nominal.face(ungluedValueAtI0, gamma),
        app(equivFun(equivG), filledValuesForEquivalences(gamma)), Nominal.face(ungluedValuesSystem, gamma))
    }

    val fiberSystem: System[Val] = {
      val common = composedValuesForEquivalencesAtI1.keySet.intersect(pathComposedForEquivalences.keySet)
      common.map(k => k -> VPair(composedValuesForEquivalencesAtI1(k), pathComposedForEquivalences(k))).toMap
    }

    val inputSystemAtI1 = Nominal.face(faceVals, Face.dir(i, Dir.One))

    val extendedFiberSystem = equivalencesAtI1.map { case (gamma, equivG) =>
      val fibsgamma: System[Val] = {
        val inputAtI1FacedGamma   = Nominal.face(inputSystemAtI1, gamma)
        val ungluedAtI1FacedGamma = Nominal.face(ungluedValuesAtI1, gamma)
        val common = inputAtI1FacedGamma.keySet.intersect(ungluedAtI1FacedGamma.keySet)
        common.map(k => k -> VPair(inputAtI1FacedGamma(k), Val.constPath(ungluedAtI1FacedGamma(k)))).toMap
      }
      gamma -> extend(
        mkFiberType(Nominal.face(ai1, gamma), Nominal.face(composedValueAtI1Preliminary, gamma), equivG),
        app(equivContr(equivG), Nominal.face(composedValueAtI1Preliminary, gamma)),
        SystemOps.unionSystem(fibsgamma, Nominal.face(fiberSystem, gamma))
      )
    }

    val composedValueAtI1 = compConstLine(ai1, composedValueAtI1Preliminary,
      SystemOps.unionSystem(
        extendedFiberSystem.map { case (gamma, v) => gamma -> sndVal(v) },
        ungluedValuesAtI1.map { case (gamma, v) => gamma -> Val.constPath(v) }))

    val glueElemsAtI1 = extendedFiberSystem.map { case (gamma, v) => gamma -> fstVal(v) }

    glueElem(composedValueAtI1, glueElemsAtI1)
  }

  def mkFiberType(baseType: Type, center: Val, equiv: Val): Type = {
    val ta = Term.Var("a")
    val tx = Term.Var("x")
    val ty = Term.Var("y")
    val tf = Term.Var("f")
    val tt = Term.Var("t")
    val env = Environment.updateAll(
      List(("a", baseType), ("x", center), ("f", equivFun(equiv)), ("t", equivDom(equiv))),
      Environment.empty)
    eval(Term.Sigma(Term.Lam(Icity.Explicit, "y", tt, Term.PathP(Term.PLam(Name("_"), ta), tx, Term.App(Icity.Explicit, tf, ty)))), env)
  }

  def pathComp(i: Name, ty: Type, baseVal: Val, endVal: Val, faceVals: System[Val]): Val = {
    val j = Nominal.fresh((Formula.Atom(i), ty, faceVals, baseVal, endVal))
    VPLam(j, comp(i, ty, baseVal,
      SystemOps.insertsSystem(List((Face.dir(j, Dir.One), endVal)), faceVals)))
  }

  /**
   * Composition in the universe (`CompU`) and the associated Glue-in-the-universe
   * construction.
   *
   * `compU i A [φ ↦ e] u₀` — composition in `U` via a system `e` of equivalence
   * paths `e : 𝕀 → U` (type lines).  Reduces to a `glueElem` at `i=1`.
   *
   * `compUniv A [φ ↦ e]` — the universe-level homotopy composition (produces the
   * type that is `A` on `φ=0` and the transported type on `φ=1`).
   *
   * `lemEq` — auxiliary lemma for coherence: given an equivalence path and a base
   * point, it produces the lifted element together with a coherence path.
   */
  def eqFun(equivPath: Val, value: Val): Val = transNegLine(equivPath, value)

  def unGlueU(w: Val, baseType: Type, equivPaths: System[Val]): Val = {
    if (equivPaths.contains(Face.eps)) eqFun(equivPaths(Face.eps), w)
    else w match {
      case VGlueElem(v, _) => v
      case _ => VUnGlueElemU(w, baseType, equivPaths)
    }
  }

  def compUniv(baseType: Type, equivPaths: System[Val]): Val = {
    if (equivPaths.contains(Face.eps)) appFormula(equivPaths(Face.eps), Formula.Dir(Dir.One))
    else VCompU(baseType, equivPaths)
  }

  def compU(i: Name, baseType: Type, equivs: System[Val], baseAtI0: Val, faceVals: System[Val]): Val = {
    val ai1 = Nominal.face(baseType, Face.dir(i, Dir.One))
    val ungluedValuesSystem = faceVals.map { case (alpha, wAlpha) =>
      alpha -> unGlueU(wAlpha, Nominal.face(baseType, alpha), Nominal.face(equivs, alpha))
    }
    val ungluedValuesAtI1 = Nominal.face(ungluedValuesSystem, Face.dir(i, Dir.One))
    val ungluedValueAtI0 = unGlueU(baseAtI0,
      Nominal.face(baseType, Face.dir(i, Dir.Zero)), Nominal.face(equivs, Face.dir(i, Dir.Zero)))
    val composedValueAtI1Preliminary = comp(i, baseType, ungluedValueAtI0, ungluedValuesSystem)
    val equationsAtI1 = Nominal.face(equivs, Face.dir(i, Dir.One))
    val equationsWithoutI = equivs.filter { case (alpha, _) => !alpha.contains(i) }

    val filledValuesForEquations = equationsWithoutI.map { case (gamma, eqG) =>
      gamma -> fill(i, appFormula(eqG, Formula.Dir(Dir.One)), Nominal.face(baseAtI0, gamma), Nominal.face(faceVals, gamma))
    }
    val composedValuesForEquationsAtI1 = equationsWithoutI.map { case (gamma, eqG) =>
      gamma -> comp(i, appFormula(eqG, Formula.Dir(Dir.One)), Nominal.face(baseAtI0, gamma), Nominal.face(faceVals, gamma))
    }

    val pathComposedForEquations = equationsWithoutI.map { case (gamma, eqG) =>
      gamma -> pathComp(i, Nominal.face(baseType, gamma), Nominal.face(ungluedValueAtI0, gamma),
        eqFun(eqG, filledValuesForEquations(gamma)), Nominal.face(ungluedValuesSystem, gamma))
    }

    val fiberSystem: System[(Val, Val)] = {
      val common = composedValuesForEquationsAtI1.keySet.intersect(pathComposedForEquations.keySet)
      common.map(k => k -> (composedValuesForEquationsAtI1(k), pathComposedForEquations(k))).toMap
    }

    val inputSystemAtI1 = Nominal.face(faceVals, Face.dir(i, Dir.One))

    val extendedFiberSystem = equationsAtI1.map { case (gamma, eqG) =>
      val fibsgamma: System[(Val, Val)] = {
        val inputAtI1FacedGamma   = Nominal.face(inputSystemAtI1, gamma)
        val ungluedAtI1FacedGamma = Nominal.face(ungluedValuesAtI1, gamma)
        val common = inputAtI1FacedGamma.keySet.intersect(ungluedAtI1FacedGamma.keySet)
        common.map(k => k -> (inputAtI1FacedGamma(k), Val.constPath(ungluedAtI1FacedGamma(k)))).toMap
      }
      gamma -> lemEq(eqG, Nominal.face(composedValueAtI1Preliminary, gamma),
        SystemOps.unionSystem(fibsgamma, Nominal.face(fiberSystem, gamma)))
    }

    val composedValueAtI1 = compConstLine(ai1, composedValueAtI1Preliminary,
      SystemOps.unionSystem(
        extendedFiberSystem.map { case (gamma, (_, p)) => gamma -> p },
        ungluedValuesAtI1.map { case (gamma, v) => gamma -> Val.constPath(v) }))

    val glueElemsAtI1 = extendedFiberSystem.map { case (gamma, (u, _)) => gamma -> u }

    glueElem(composedValueAtI1, glueElemsAtI1)
  }

  def lemEq(equivPath: Val, baseVal: Val, adjunctionPairs: System[(Val, Val)]): (Val, Val) = {
    given Nominal[(Val, Val)] = Nominal.nominalPair[Val, Val]

    val names = Nominal.freshs((equivPath, baseVal, adjunctionPairs))
    val i = names(0)
    val j = names(1)
    val ta = appFormula(equivPath, Formula.Dir(Dir.One))

    val p1Systems = adjunctionPairs.map { case (alpha, (aa, pa)) =>
      val eqaj = appFormula(Nominal.face(equivPath, alpha), Formula.Atom(j))
      val ba = Nominal.face(baseVal, alpha)
      alpha -> comp(j, eqaj, appFormula(pa, Formula.Atom(i)),
        SystemOps.mkSystem(List(
          (Face.dir(i, Dir.Zero), transFill(j, eqaj, ba)),
          (Face.dir(i, Dir.One), transFillNeg(j, eqaj, aa)))))
    }
    val thetaSystems = adjunctionPairs.map { case (alpha, (aa, pa)) =>
      val eqaj = appFormula(Nominal.face(equivPath, alpha), Formula.Atom(j))
      val ba = Nominal.face(baseVal, alpha)
      alpha -> fill(j, eqaj, appFormula(pa, Formula.Atom(i)),
        SystemOps.mkSystem(List(
          (Face.dir(i, Dir.Zero), transFill(j, eqaj, ba)),
          (Face.dir(i, Dir.One), transFillNeg(j, eqaj, aa)))))
    }

    val composedVal = comp(i, ta, trans(i, appFormula(equivPath, Formula.Atom(i)), baseVal), p1Systems)
    val filledPath  = fill(i, ta, trans(i, appFormula(equivPath, Formula.Atom(i)), baseVal), p1Systems)

    val extendedThetaSystems = SystemOps.insertsSystem(
      List(
        (Face.dir(i, Dir.Zero), transFill(j, appFormula(equivPath, Formula.Atom(j)), baseVal)),
        (Face.dir(i, Dir.One), transFillNeg(j, appFormula(equivPath, Formula.Atom(j)), composedVal))),
      thetaSystems)

    (composedVal, VPLam(i, compNeg(j, appFormula(equivPath, Formula.Atom(j)), filledPath, extendedThetaSystems)))
  }

  /**
   * Definitional equality (conversion) check.
   *
   * {{{
   *   Γ ⊢ u : A    Γ ⊢ v : A
   *   ──────────────────────── (Conv)
   *   Γ ⊢ u =_β v
   * }}}
   *
   * `convert ns u v`  decides `u =_β v` up to α-equivalence, with η-expansion for
   * functions (`u ≡ v` iff `u x ≡ v x` for fresh `x`), pairs (`fst/snd`), and
   * paths (`p @@ j ≡ q @@ j` for fresh `j`).  `ns` is the list of names already
   * in scope used for fresh variable generation.
   */
  def convert(ns: List[String], u: Val, v: Val): Boolean = {
    if (u == v) return true
    val j = Nominal.fresh((u, v))
    (u, v) match {
      case (Closure(Term.Lam(_, x, a, u1), e), Closure(Term.Lam(_, x2, a2, u2), e2)) =>
        val w @ VVar(n, _) = mkVarNice(ns, x, eval(a, e)): @unchecked
        convert(n :: ns, eval(u1, Environment.update((x, w), e)), eval(u2, Environment.update((x2, w), e2)))
      case (Closure(Term.Lam(_, x, a, u1), e), u2) =>
        val w @ VVar(n, _) = mkVarNice(ns, x, eval(a, e)): @unchecked
        convert(n :: ns, eval(u1, Environment.update((x, w), e)), app(u2, w))
      case (u1, Closure(Term.Lam(_, x, a, u2), e)) =>
        val w @ VVar(n, _) = mkVarNice(ns, x, eval(a, e)): @unchecked
        convert(n :: ns, app(u1, w), eval(u2, Environment.update((x, w), e)))
      case (Closure(Term.Split(_, p, _, _), e), Closure(Term.Split(_, p2, _, _), e2)) =>
        p == p2 && convertEnv(ns, e, e2)
      case (Closure(Term.Sum(p, _, _), e), Closure(Term.Sum(p2, _, _), e2)) =>
        p == p2 && convertEnv(ns, e, e2)
      case (Closure(Term.HSum(p, _, _), e), Closure(Term.HSum(p2, _, _), e2)) =>
        p == p2 && convertEnv(ns, e, e2)
      case (Closure(Term.Undef(p, _), e), Closure(Term.Undef(p2, _), e2)) =>
        p == p2 && convertEnv(ns, e, e2)
      case (Closure(Term.Hole(p), e), Closure(Term.Hole(p2), e2)) =>
        p == p2 && convertEnv(ns, e, e2)
      case (VPi(_, u1, v1), VPi(_, u2, v2)) =>
        val w @ VVar(n, _) = mkVarNice(ns, "X", u1): @unchecked
        convert(ns, u1, u2) && convert(n :: ns, app(v1, w), app(v2, w))
      case (VSigma(u1, v1), VSigma(u2, v2)) =>
        val w @ VVar(n, _) = mkVarNice(ns, "X", u1): @unchecked
        convert(ns, u1, u2) && convert(n :: ns, app(v1, w), app(v2, w))
      case (VCon(c, us1), VCon(c2, us2)) =>
        c == c2 && convertList(ns, us1, us2)
      case (VPCon(c, v1, us1, phis1), VPCon(c2, v2, us2, phis2)) =>
        c == c2 && convert(ns, v1, v2) && convertList(ns, us1, us2) && convertFormulas(ns, phis1, phis2)
      case (VPair(u1, v1), VPair(u2, v2)) =>
        convert(ns, u1, u2) && convert(ns, v1, v2)
      case (VPair(u1, v1), w) =>
        convert(ns, u1, fstVal(w)) && convert(ns, v1, sndVal(w))
      case (w, VPair(u2, v2)) =>
        convert(ns, fstVal(w), u2) && convert(ns, sndVal(w), v2)
      case (VFst(u1), VFst(u2)) => convert(ns, u1, u2)
      case (VSnd(u1), VSnd(u2)) => convert(ns, u1, u2)
      case (VApp(u1, v1), VApp(u2, v2)) => convert(ns, u1, u2) && convert(ns, v1, v2)
      case (VSplit(u1, v1), VSplit(u2, v2)) => convert(ns, u1, u2) && convert(ns, v1, v2)
      case (VOpaque(x, _), VOpaque(x2, _)) => x == x2
      case (VVar(x, _), VVar(x2, _)) => x == x2
      case (VPathP(a, b, c), VPathP(a2, b2, c2)) =>
        convert(ns, a, a2) && convert(ns, b, b2) && convert(ns, c, c2)
      case (VPLam(i, a), VPLam(i2, a2)) =>
        convert(ns, Nominal.swap(a, (i, j)), Nominal.swap(a2, (i2, j)))
      case (VPLam(i, a), p2) =>
        convert(ns, Nominal.swap(a, (i, j)), appFormula(p2, Formula.Atom(j)))
      case (p, VPLam(i2, a2)) =>
        convert(ns, appFormula(p, Formula.Atom(j)), Nominal.swap(a2, (i2, j)))
      case (VAppFormula(u1, x), VAppFormula(u2, x2)) =>
        convert(ns, u1, u2) && convertFormula(ns, x, x2)
      case (VComp(a, u1, ts), VComp(a2, u2, ts2)) =>
        convert(ns, a, a2) && convert(ns, u1, u2) && convertSystem(ns, ts, ts2)
      case (VHComp(a, u1, ts), VHComp(a2, u2, ts2)) =>
        convert(ns, a, a2) && convert(ns, u1, u2) && convertSystem(ns, ts, ts2)
      case (VGlue(v1, equivs1), VGlue(v2, equivs2)) =>
        convert(ns, v1, v2) && convertSystem(ns, equivs1, equivs2)
      case (VGlueElem(VUnGlueElem(b, equivs), ts), g) =>
        convertSystem(ns, Nominal.border(b, equivs), ts) && convert(ns, b, g)
      case (g, VGlueElem(VUnGlueElem(b, equivs), ts)) =>
        convertSystem(ns, Nominal.border(b, equivs), ts) && convert(ns, b, g)
      case (VGlueElem(VUnGlueElemU(b, _, equivs), ts), g) =>
        convertSystem(ns, Nominal.border(b, equivs), ts) && convert(ns, b, g)
      case (g, VGlueElem(VUnGlueElemU(b, _, equivs), ts)) =>
        convertSystem(ns, Nominal.border(b, equivs), ts) && convert(ns, b, g)
      case (VGlueElem(u1, us1), VGlueElem(u2, us2)) =>
        convert(ns, u1, u2) && convertSystem(ns, us1, us2)
      case (VUnGlueElemU(u1, _, _), VUnGlueElemU(u2, _, _)) => convert(ns, u1, u2)
      case (VUnGlueElem(u1, _), VUnGlueElem(u2, _)) => convert(ns, u1, u2)
      case (VCompU(u1, es1), VCompU(u2, es2)) =>
        convert(ns, u1, u2) && convertSystem(ns, es1, es2)
      case (VIdPair(v1, vs1), VIdPair(v2, vs2)) =>
        convert(ns, v1, v2) && convertSystem(ns, vs1, vs2)
      case (VId(a, u1, v1), VId(a2, u2, v2)) =>
        convert(ns, a, a2) && convert(ns, u1, u2) && convert(ns, v1, v2)
      case (VIdJ(a, u1, c, d, x, p), VIdJ(a2, u2, c2, d2, x2, p2)) =>
        convertList(ns, List(a, u1, c, d, x, p), List(a2, u2, c2, d2, x2, p2))
      case (VMeta(id1), VMeta(id2)) => id1 == id2
      case _ => false
    }
  }

  def convertEnv(ns: List[String], e1: Environment, e2: Environment): Boolean = {
    convertContext(ns, e1.ctx, e2.ctx) &&
    convertList(ns, e1.vals, e2.vals) &&
    convertFormulas(ns, e1.formulas, e2.formulas)
  }

  def convertContext(ns: List[String], c1: Context, c2: Context): Boolean = true

  def convertList(ns: List[String], us: List[Val], vs: List[Val]): Boolean = {
    us.length == vs.length && us.zip(vs).forall { case (u, v) => convert(ns, u, v) }
  }

  def convertFormula(ns: List[String], phi: Formula, psi: Formula): Boolean = {
    Formula.dnf(phi) == Formula.dnf(psi)
  }

  def convertFormulas(ns: List[String], phis: List[Formula], psis: List[Formula]): Boolean = {
    phis.length == psis.length && phis.zip(psis).forall { case (p, q) => convertFormula(ns, p, q) }
  }

  def convertSystem(ns: List[String], ts: System[Val], ts2: System[Val]): Boolean = {
    ts.keys.toSet == ts2.keys.toSet &&
    ts.forall { case (k, v) => ts2.get(k).exists(v2 => convert(ns, v, v2)) }
  }

  def isCompSystem(ns: List[String], ts: System[Val]): Boolean = {
    val faceKeys = ts.keys.toList
    allCompatible(faceKeys).forall { case (alpha, beta) =>
      convert(ns,
        Nominal.face(ts(alpha), Face.minus(beta, alpha)),
        Nominal.face(ts(beta), Face.minus(alpha, beta)))
    }
  }

  /**
   * Normalisation: reduce a value to its fully normal form.
   *
   * Traverses the value tree recursively, applying η-expansion for lambdas and
   * normalising all sub-values.  Used for pretty-printing and hole display.
   *
   * Note: this is "read-back" normalisation (reify), not a separate pass.
   */
  def normal(ns: List[String], v: Val): Val = v match {
    case VU => VU
    case Closure(Term.Lam(_, x, t, u1), e) =>
      val w = eval(t, e)
      val freshVarVal @ VVar(n, _) = mkVarNice(ns, x, w): @unchecked
      VLam(n, normal(ns, w), normal(n :: ns, eval(u1, Environment.update((x, freshVarVal), e))))
    case Closure(t, e) => Closure(t, normalEnv(ns, e))
    case VPi(icity, u1, v1) => VPi(icity, normal(ns, u1), normal(ns, v1))
    case VSigma(u1, v1) => VSigma(normal(ns, u1), normal(ns, v1))
    case VPair(u1, v1) => VPair(normal(ns, u1), normal(ns, v1))
    case VCon(n, us) => VCon(n, us.map(normal(ns, _)))
    case VPCon(n, u1, us, phis) =>
      VPCon(n, normal(ns, u1), us.map(normal(ns, _)), phis.map(normalFormula))
    case VPathP(a, u1, v1) => VPathP(normal(ns, a), normal(ns, u1), normal(ns, v1))
    case VPLam(i, u1) => VPLam(i, normal(ns, u1))
    case VComp(u1, v1, vs) => VComp(normal(ns, u1), normal(ns, v1), normalSystem(ns, vs))
    case VHComp(u1, v1, vs) => VHComp(normal(ns, u1), normal(ns, v1), normalSystem(ns, vs))
    case VGlue(u1, equivs) => VGlue(normal(ns, u1), normalSystem(ns, equivs))
    case VGlueElem(u1, us) => VGlueElem(normal(ns, u1), normalSystem(ns, us))
    case VUnGlueElem(u1, us) => VUnGlueElem(normal(ns, u1), normalSystem(ns, us))
    case VUnGlueElemU(e, u1, us) =>
      VUnGlueElemU(normal(ns, e), normal(ns, u1), normalSystem(ns, us))
    case VCompU(a, ts) => VCompU(normal(ns, a), normalSystem(ns, ts))
    case VVar(x, t) => VVar(x, normal(ns, t))
    case VFst(t) => VFst(normal(ns, t))
    case VSnd(t) => VSnd(normal(ns, t))
    case VSplit(u1, t) => VSplit(normal(ns, u1), normal(ns, t))
    case VApp(u1, v1) => VApp(normal(ns, u1), normal(ns, v1))
    case VAppFormula(u1, phi) => VAppFormula(normal(ns, u1), normalFormula(phi))
    case VId(a, u1, v1) => VId(normal(ns, a), normal(ns, u1), normal(ns, v1))
    case VIdPair(u1, us) => VIdPair(normal(ns, u1), normalSystem(ns, us))
    case VIdJ(a, u1, c, d, x, p) =>
      VIdJ(normal(ns, a), normal(ns, u1), normal(ns, c),
           normal(ns, d), normal(ns, x), normal(ns, p))
    case VMeta(_) => v
    case _ => v
  }

  def normalEnv(ns: List[String], env: Environment): Environment = {
    Environment.mapEnv(normal(ns, _), normalFormula, env)
  }

  def normalFormula(phi: Formula): Formula = Formula.fromDNF(Formula.dnf(phi))

  def normalSystem(ns: List[String], ts: System[Val]): System[Val] = {
    ts.map { case (k, v) => k -> normal(ns, v) }
  }

  /**
   * Generate a fresh variable name that does not clash with `ns`.
   *
   * Tries `x`, then `x0`, `x1`, … until a name not in `ns` is found.
   * Returns `VVar(name, ty)`.
   */
  def mkVarNice(ns: List[String], x: String, ty: Type): Val = {
    val candidateNames = x #:: LazyList.from(0).map(n => x + n.toString)
    val name = candidateNames.find(y => !ns.contains(y)).get
    VVar(name, ty)
  }

  private def allCompatible(fs: List[Face]): List[(Face, Face)] = fs match {
    case Nil     => Nil
    case f :: rest =>
      rest.filter(Face.compatible(f, _)).map(g => (f, g)) ++ allCompatible(rest)
  }
}

case class EvalError(msg: String) extends RuntimeException(msg)
