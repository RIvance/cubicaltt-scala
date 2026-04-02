package cubical

import scala.collection.immutable.Map

import Val.*
import Branch.{OBranch, PBranch}

object Eval {

  // ── Lookup functions ─────────────────────────────────────

  def look(x: String, env: Environment): Val = {
    def go(ctx: Context, vs: List[Val], fs: List[Formula], os: Nameless[Set[Ident]]): Val = ctx match {
      case Context.Empty => throw EvalError(s"look: not found $x")
      case Context.Update(y, parent) =>
        vs match {
          case v :: rest => if (x == y) v else go(parent, rest, fs, os)
          case Nil       => throw EvalError(s"look: env out of sync for $x")
        }
      case Context.Define(loc, decls, parent) =>
        Declarations.declDefs(decls).find(_._1 == x) match {
          case Some((_, t)) => eval(t, Environment(ctx, vs, fs, os))
          case None         => go(parent, vs, fs, os)
        }
      case Context.Substitute(_, parent) =>
        fs match {
          case _ :: rest => go(parent, vs, rest, os)
          case Nil       => throw EvalError(s"look: env out of sync for $x (Substitute)")
        }
    }
    go(env.ctx, env.vals, env.formulas, env.opaques)
  }

  def lookType(x: String, env: Environment): Val = {
    def go(ctx: Context, vs: List[Val], fs: List[Formula], os: Nameless[Set[Ident]]): Val = ctx match {
      case Context.Empty => throw EvalError(s"lookType: not found $x")
      case Context.Update(y, parent) =>
        vs match {
          case v :: rest =>
            if (x == y) {
              v match {
                case VVar(_, a) => a
                case _          => throw EvalError(s"lookType: $x is not a VVar")
              }
            } else go(parent, rest, fs, os)
          case Nil => throw EvalError(s"lookType: env out of sync for $x")
        }
      case Context.Define(loc, decls, parent) =>
        Declarations.declTelescope(decls).find(_._1 == x) match {
          case Some((_, a)) => eval(a, Environment(ctx, vs, fs, os))
          case None         => go(parent, vs, fs, os)
        }
      case Context.Substitute(_, parent) =>
        fs match {
          case _ :: rest => go(parent, vs, rest, os)
          case Nil       => throw EvalError(s"lookType: env out of sync for $x (Substitute)")
        }
    }
    go(env.ctx, env.vals, env.formulas, env.opaques)
  }

  def lookName(i: Name, env: Environment): Formula = Environment.lookupName(i, env)

  // ── Nominal instances ────────────────────────────────────

  given nominalContext: Nominal[Context] with {
    def support(a: Context): List[Name] = Nil
    def act(a: Context, sub: (Name, Formula)): Context = a
    def swap(a: Context, names: (Name, Name)): Context = a
  }

  given nominalEnvironment: Nominal[Environment] with {
    def support(e: Environment): List[Name] = {
      Nominal.support[(Context, List[Val], List[Formula], Nameless[Set[Ident]])](
        (e.ctx, e.vals, e.formulas, e.opaques)
      )
    }
    def act(e: Environment, sub: (Name, Formula)): Environment = {
      val r = Nominal.act[(Context, List[Val], List[Formula], Nameless[Set[Ident]])](
        (e.ctx, e.vals, e.formulas, e.opaques), sub
      )
      Environment(r._1, r._2, r._3, r._4)
    }
    def swap(e: Environment, names: (Name, Name)): Environment = {
      val r = Nominal.swap[(Context, List[Val], List[Formula], Nameless[Set[Ident]])](
        (e.ctx, e.vals, e.formulas, e.opaques), names
      )
      Environment(r._1, r._2, r._3, r._4)
    }
  }

  given nominalSetIdent: Nominal[Set[Ident]] with {
    def support(a: Set[Ident]): List[Name] = Nil
    def act(a: Set[Ident], sub: (Name, Formula)): Set[Ident] = a
    def swap(a: Set[Ident], names: (Name, Name)): Set[Ident] = a
  }

  given nominalVal: Nominal[Val] with {
    def support(v: Val): List[Name] = v match {
      case VU                     => Nil
      case Closure(_, e)          => Nominal.support(e)
      case VPi(u, v)              => Nominal.support((u, v))
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
    }

    def act(u: Val, iphi: (Name, Formula)): Val = {
      val (i, phi) = iphi
      if (!support(u).contains(i)) return u
      def acti[A: Nominal](a: A): A = Nominal.act(a, iphi)
      val sphi = Nominal.support(phi)
      u match {
        case VU              => VU
        case Closure(t, e)   => Closure(t, acti(e))
        case VPi(a, f)       => VPi(acti(a), acti(f))
        case VComp(a, v, ts) => compLine(acti(a), acti(v), acti(ts))
        case VPathP(a, u, v) => VPathP(acti(a), acti(u), acti(v))
        case VPLam(j, v) =>
          if (j == i) u
          else if (!sphi.contains(j)) VPLam(j, acti(v))
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
        case VIdJ(a, u, c, d, x, p)  =>
          idJ(acti(a), acti(u), acti(c), acti(d), acti(x), acti(p))
      }
    }

    def swap(u: Val, ij: (Name, Name)): Val = {
      def sw[A: Nominal](a: A): A = Nominal.swap(a, ij)
      u match {
        case VU                       => VU
        case Closure(t, e)            => Closure(t, sw(e))
        case VPi(a, f)                => VPi(sw(a), sw(f))
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
        case VIdJ(a, u, c, d, x, p)  =>
          VIdJ(sw(a), sw(u), sw(c), sw(d), sw(x), sw(p))
      }
    }
  }

  // ── The evaluator ────────────────────────────────────────

  def eval(t: Term, env: Environment): Val = {
    val os = env.opaques.value
    t match {
      case Term.U => VU
      case Term.App(r, s) => app(eval(r, env), eval(s, env))
      case Term.Var(x) =>
        if (os.contains(x)) VOpaque(x, lookType(x, env))
        else look(x, env)
      case Term.Pi(lam @ Term.Lam(_, a, _)) => VPi(eval(a, env), Closure(lam, env))
      case Term.Sigma(lam @ Term.Lam(_, a, _)) => VSigma(eval(a, env), Closure(lam, env))
      case Term.Pair(a, b) => VPair(eval(a, env), eval(b, env))
      case Term.Fst(a) => fstVal(eval(a, env))
      case Term.Snd(a) => sndVal(eval(a, env))
      case Term.Where(t, decls) => eval(t, Environment.addDeclWhere(decls, env))
      case Term.Con(name, ts) => VCon(name, ts.map(eval(_, env)))
      case Term.PCon(name, a, ts, phis) =>
        pcon(name, eval(a, env), ts.map(eval(_, env)), phis.map(evalFormula(env, _)))
      case t @ Term.Lam(_, _, _)       => Closure(t, env)
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
      case _ => throw EvalError(s"Cannot evaluate $t")
    }
  }

  def evals(env: Environment, bts: List[(Ident, Term)]): List[(Ident, Val)] = {
    bts.map { case (b, t) => (b, eval(t, env)) }
  }

  def evalFormula(env: Environment, phi: Formula): Formula = phi match {
    case Formula.Atom(i)    => lookName(i, env)
    case Formula.NegAtom(i) => Formula.negFormula(lookName(i, env))
    case Formula.And(p, q)  => Formula.andFormula(evalFormula(env, p), evalFormula(env, q))
    case Formula.Or(p, q)   => Formula.orFormula(evalFormula(env, p), evalFormula(env, q))
    case _                  => phi
  }

  def evalSystem(env: Environment, ts: System[Term]): System[Val] = {
    val out = ts.toList.flatMap { case (alpha, talpha) =>
      val betas = Face.meetss(
        alpha.toList.map { case (i, d) =>
          Formula.invFormula(lookName(i, env), d)
        }
      )
      betas.map { beta =>
        (beta, eval(talpha, Nominal.face(env, beta)))
      }
    }
    SystemOps.mkSystem(out)
  }

  // ── Application ──────────────────────────────────────────

  def app(u: Val, v: Val): Val = (u, v) match {
    case (Closure(Term.Lam(x, _, t), e), _) =>
      eval(t, Environment.update((x, v), e))
    case (Closure(Term.Split(_, _, _, nvs), e), VCon(c, vs)) =>
      Branch.lookupBranch(c, nvs) match {
        case Some(OBranch(_, xs, t)) =>
          eval(t, Environment.updateAll(xs.zip(vs), e))
        case _ => throw EvalError(s"app: missing case in split for $c")
      }
    case (Closure(Term.Split(_, _, _, nvs), e), VPCon(c, _, us, phis)) =>
      Branch.lookupBranch(c, nvs) match {
        case Some(PBranch(_, xs, is, t)) =>
          eval(t, Environment.substituteAll(is.zip(phis), Environment.updateAll(xs.zip(us), e)))
        case _ => throw EvalError(s"app: missing case in split for $c")
      }
    case (Closure(Term.Split(_, _, ty, _), e), VHComp(a, w, ws)) =>
      eval(ty, e) match {
        case VPi(_, f) =>
          val j = Nominal.fresh((e, v))
          val wsj = ws.map { case (alpha, uAlpha) => alpha -> appFormula(uAlpha, Formula.Atom(j)) }
          val w2 = app(u, w)
          val ws2 = wsj.map { case (alpha, wAlpha) =>
            alpha -> app(Nominal.face(u, alpha), wAlpha)
          }
          comp(j, app(f, fill(j, a, w, wsj)), w2, ws2)
        case _ => throw EvalError(s"app: Split annotation not a Pi type $u")
      }
    case (Closure(Term.Split(_, _, _, _), _), _) if Val.isNeutral(v) => VSplit(u, v)
    case (VComp(VPLam(i, VPi(a, f)), li0, ts), vi1) =>
      val j = Nominal.fresh((u, vi1))
      val (aj, fj) = (Nominal.swap(a, (i, j)), Nominal.swap(f, (i, j)))
      val tsj = ts.map { case (alpha, tAlpha) => alpha -> appFormula(tAlpha, Formula.Atom(j)) }
      val v2 = transFillNeg(j, aj, vi1)
      val vi0 = transNeg(j, aj, vi1)
      comp(j, app(fj, v2), app(li0, vi0),
        tsj.map { case (alpha, tAlpha) => alpha -> app(tAlpha, Nominal.face(v2, alpha)) })
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

  // ── InferType (for neutral values) ───────────────────────

  def inferType(v: Val): Val = v match {
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
      case VPi(_, f) => app(f, v1)
      case ty => throw EvalError(s"inferType: Pi type expected for split in $v, got $ty")
    }
    case VApp(t0, t1) => inferType(t0) match {
      case VPi(_, f) => app(f, t1)
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

  // ── Path application (@@) ────────────────────────────────

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

  // ── Composition and filling ──────────────────────────────

  def comp(i: Name, a: Val, u: Val, ts: System[Val]): Val = {
    if (ts.contains(Face.eps)) {
      Nominal.face(ts(Face.eps), Face.dir(i, Dir.One))
    } else a match {
      case VPathP(p, v0, v1) =>
        val j = Nominal.fresh((Formula.Atom(i), a, u, ts))
        VPLam(j, comp(i, appFormula(p, Formula.Atom(j)), appFormula(u, Formula.Atom(j)),
          SystemOps.insertsSystem(
            List((Face.dir(j, Dir.Zero), v0),
                 (Face.dir(j, Dir.One), v1)),
            ts.map { case (alpha, tAlpha) => alpha -> appFormula(tAlpha, Formula.Atom(j)) })))
      case VId(b, v0, v1) =>
        u match {
          case VIdPair(r, _) if ts.values.forall(isIdPair) =>
            val j = Nominal.fresh((Formula.Atom(i), a, u, ts))
            val w = VPLam(j, comp(i, b, appFormula(r, Formula.Atom(j)),
              SystemOps.insertsSystem(
                List((Face.dir(j, Dir.Zero), v0),
                     (Face.dir(j, Dir.One), v1)),
                ts.map { case (alpha, tAlpha) => alpha -> appFormulaIdPair(tAlpha, j) })))
            val tsFaced = Nominal.face(ts, Face.dir(i, Dir.One))
            VIdPair(w, SystemOps.joinSystem(
              tsFaced.map { case (alpha, tAlpha) =>
                alpha -> sysOfIdPair(tAlpha)
              }))
          case _ => VComp(VPLam(i, a), u, ts.map { case (alpha, tAlpha) => alpha -> VPLam(i, tAlpha) })
        }
      case VSigma(sa, f) =>
        val t1s = ts.map { case (alpha, tAlpha) => alpha -> fstVal(tAlpha) }
        val t2s = ts.map { case (alpha, tAlpha) => alpha -> sndVal(tAlpha) }
        val (u1, u2) = (fstVal(u), sndVal(u))
        val fillU1 = fill(i, sa, u1, t1s)
        val ui1 = comp(i, sa, u1, t1s)
        val compU2 = comp(i, app(f, fillU1), u2, t2s)
        VPair(ui1, compU2)
      case VPi(_, _) =>
        VComp(VPLam(i, a), u, ts.map { case (alpha, tAlpha) => alpha -> VPLam(i, tAlpha) })
      case VU =>
        compUniv(u, ts.map { case (alpha, tAlpha) => alpha -> VPLam(i, tAlpha) })
      case VCompU(ca, es) if !isNeutralU(i, es, u, ts) =>
        compU(i, ca, es, u, ts)
      case VGlue(b, equivs) if !isNeutralGlue(i, equivs, u, ts) =>
        compGlue(i, b, equivs, u, ts)
      case Closure(Term.Sum(_, _, nass), env) =>
        u match {
          case VCon(n, us) if ts.values.forall { case VCon(_, _) => true; case _ => false } =>
            Label.lookupLabel(n, nass) match {
              case Some(as) =>
                val tsus = SystemOps.transposeSystemAndList(
                  ts.map { case (alpha, tAlpha) => alpha -> Val.unCon(tAlpha) }, us)
                VCon(n, comps(i, as, env, tsus))
              case None => throw EvalError(s"comp: missing constructor in labelled sum $n")
            }
          case _ =>
            VComp(VPLam(i, a), u, ts.map { case (alpha, tAlpha) => alpha -> VPLam(i, tAlpha) })
        }
      case Closure(Term.HSum(_, _, _), _) => compHIT(i, a, u, ts)
      case _ =>
        VComp(VPLam(i, a), u, ts.map { case (alpha, tAlpha) => alpha -> VPLam(i, tAlpha) })
    }
  }

  def compNeg(i: Name, a: Val, u: Val, ts: System[Val]): Val = {
    comp(i, Nominal.sym(a, i), u, Nominal.sym(ts, i))
  }

  def compLine(a: Val, u: Val, ts: System[Val]): Val = {
    val i = Nominal.fresh((a, u, ts))
    comp(i, appFormula(a, Formula.Atom(i)), u,
      ts.map { case (alpha, tAlpha) => alpha -> appFormula(tAlpha, Formula.Atom(i)) })
  }

  def compConstLine(a: Val, u: Val, ts: System[Val]): Val = {
    val i = Nominal.fresh((a, u, ts))
    comp(i, a, u,
      ts.map { case (alpha, tAlpha) => alpha -> appFormula(tAlpha, Formula.Atom(i)) })
  }

  def comps(i: Name, as: List[(Ident, Term)], env: Environment, tsus: List[(System[Val], Val)]): List[Val] = {
    (as, tsus) match {
      case (Nil, Nil) => Nil
      case ((x, a) :: asTail, (ts, u) :: tsusTail) =>
        val v = fill(i, eval(a, env), u, ts)
        val vi1 = comp(i, eval(a, env), u, ts)
        val vs = comps(i, asTail, Environment.update((x, v), env), tsusTail)
        vi1 :: vs
      case _ => throw EvalError("comps: different lengths of types and values")
    }
  }

  def fill(i: Name, a: Val, u: Val, ts: System[Val]): Val = {
    val j = Nominal.fresh((Formula.Atom(i), a, u, ts))
    comp(j, Nominal.conj(a, (i, j)), u,
      SystemOps.insertSystem(Face.dir(i, Dir.Zero), u,
        Nominal.conj(ts, (i, j))))
  }

  def fillNeg(i: Name, a: Val, u: Val, ts: System[Val]): Val = {
    Nominal.sym(fill(i, Nominal.sym(a, i), u, Nominal.sym(ts, i)), i)
  }

  def fillLine(a: Val, u: Val, ts: System[Val]): Val = {
    val i = Nominal.fresh((a, u, ts))
    VPLam(i, fill(i, appFormula(a, Formula.Atom(i)), u,
      ts.map { case (alpha, tAlpha) => alpha -> appFormula(tAlpha, Formula.Atom(i)) }))
  }

  // ── Transport ────────────────────────────────────────────

  def trans(i: Name, v0: Val, v1: Val): Val = comp(i, v0, v1, Map.empty)

  def transNeg(i: Name, a: Val, u: Val): Val = trans(i, Nominal.sym(a, i), u)

  def transLine(u: Val, v: Val): Val = {
    val i = Nominal.fresh((u, v))
    trans(i, appFormula(u, Formula.Atom(i)), v)
  }

  def transNegLine(u: Val, v: Val): Val = {
    val i = Nominal.fresh((u, v))
    transNeg(i, appFormula(u, Formula.Atom(i)), v)
  }

  def transps(i: Name, as: List[(Ident, Term)], env: Environment, us: List[Val]): List[Val] = {
    (as, us) match {
      case (Nil, Nil) => Nil
      case ((x, a) :: asTail, u :: usTail) =>
        val v = transFill(i, eval(a, env), u)
        val vi1 = trans(i, eval(a, env), u)
        val vs = transps(i, asTail, Environment.update((x, v), env), usTail)
        vi1 :: vs
      case _ => throw EvalError("transps: different lengths")
    }
  }

  def transFill(i: Name, a: Val, u: Val): Val = fill(i, a, u, Map.empty)

  def transFillNeg(i: Name, a: Val, u: Val): Val = {
    Nominal.sym(transFill(i, Nominal.sym(a, i), u), i)
  }

  def squeeze(i: Name, a: Val, u: Val): Val = {
    val j = Nominal.fresh((Formula.Atom(i), a, u))
    val ui1 = Nominal.face(u, Face.dir(i, Dir.One))
    comp(j, Nominal.disj(a, (i, j)), u,
      SystemOps.mkSystem(List((Face.dir(i, Dir.One), ui1))))
  }

  def squeezes(i: Name, xas: List[(Ident, Term)], env: Environment, us: List[Val]): List[Val] = {
    val j = Nominal.fresh((us, env, Formula.Atom(i)))
    val us2 = us.map { u =>
      (SystemOps.mkSystem(List(
        (Face.dir(i, Dir.One), Nominal.face(u, Face.dir(i, Dir.One)))
      )), u)
    }
    comps(j, xas, Nominal.disj(env, (i, j)), us2)
  }

  // ── Id ───────────────────────────────────────────────────

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

  // ── HITs ─────────────────────────────────────────────────

  def pcon(c: LIdent, a: Val, us: List[Val], phis: List[Formula]): Val = a match {
    case Closure(Term.HSum(_, _, lbls), env) =>
      Label.lookupPLabel(c, lbls) match {
        case Some((tele, is, ts)) =>
          val env2 = Environment.substituteAll(is.zip(phis), Environment.updateTelescope(tele, us, env))
          val vs = evalSystem(env2, ts)
          if (vs.contains(Face.eps)) vs(Face.eps)
          else VPCon(c, a, us, phis)
        case None => throw EvalError("pcon: label not found")
      }
    case _ => VPCon(c, a, us, phis)
  }

  def compHIT(i: Name, a: Val, u: Val, us: System[Val]): Val = {
    if (Val.isNeutral(u) || Val.isNeutralSystem(us)) {
      VComp(VPLam(i, a), u, us.map { case (alpha, uAlpha) => alpha -> VPLam(i, uAlpha) })
    } else {
      hComp(
        Nominal.face(a, Face.dir(i, Dir.One)),
        transpHIT(i, a, u),
        us.map { case (alpha, uAlpha) =>
          alpha -> VPLam(i, squeezeHIT(i, Nominal.face(a, alpha), uAlpha))
        })
    }
  }

  def transpHIT(i: Name, a: Val, u: Val): Val = a match {
    case Closure(Term.HSum(_, _, nass), env) =>
      u match {
        case VCon(n, us) =>
          Label.lookupLabel(n, nass) match {
            case Some(as) => VCon(n, transps(i, as, env, us))
            case None => throw EvalError(s"transpHIT: missing constructor $n")
          }
        case VPCon(c, _, ws0, phis) =>
          Label.lookupLabel(c, nass) match {
            case Some(as) =>
              pcon(c, Nominal.face(a, Face.dir(i, Dir.One)),
                transps(i, as, env, ws0), phis)
            case None => throw EvalError(s"transpHIT: missing path constructor $c")
          }
        case VHComp(_, v, vs) =>
          val j = Nominal.fresh((a, u))
          val aij = Nominal.swap(a, (i, j))
          hComp(
            Nominal.face(a, Face.dir(i, Dir.One)),
            transpHIT(i, a, v),
            vs.map { case (alpha, vAlpha) =>
              alpha -> VPLam(j, transpHIT(j, Nominal.face(aij, alpha), appFormula(vAlpha, Formula.Atom(j))))
            })
        case _ => throw EvalError(s"transpHIT: neutral $u")
      }
    case _ => throw EvalError(s"transpHIT: not an HSum $a")
  }

  def squeezeHIT(i: Name, a: Val, u: Val): Val = a match {
    case Closure(Term.HSum(_, _, nass), env) =>
      u match {
        case VCon(n, us) =>
          Label.lookupLabel(n, nass) match {
            case Some(as) => VCon(n, squeezes(i, as, env, us))
            case None => throw EvalError(s"squeezeHIT: missing constructor $n")
          }
        case VPCon(c, _, ws0, phis) =>
          Label.lookupLabel(c, nass) match {
            case Some(as) =>
              pcon(c, Nominal.face(a, Face.dir(i, Dir.One)),
                squeezes(i, as, env, ws0), phis)
            case None => throw EvalError(s"squeezeHIT: missing path constructor $c")
          }
        case VHComp(_, v, vs) =>
          val j = Nominal.fresh((a, u))
          hComp(
            Nominal.face(a, Face.dir(i, Dir.One)),
            squeezeHIT(i, a, v),
            vs.map { case (alpha, vAlpha) =>
              alpha.get(i) match {
                case None =>
                  alpha -> VPLam(j, squeezeHIT(i, Nominal.face(a, alpha), appFormula(vAlpha, Formula.Atom(j))))
                case Some(Dir.Zero) =>
                  alpha -> VPLam(j, transpHIT(i, Nominal.face(a, alpha.removed(i)), appFormula(vAlpha, Formula.Atom(j))))
                case Some(Dir.One) =>
                  alpha -> vAlpha
              }
            })
        case _ => throw EvalError(s"squeezeHIT: neutral $u")
      }
    case _ => throw EvalError(s"squeezeHIT: not an HSum $a")
  }

  def hComp(a: Val, u: Val, us: System[Val]): Val = {
    if (us.contains(Face.eps)) appFormula(us(Face.eps), Formula.Dir(Dir.One))
    else VHComp(a, u, us)
  }

  // ── Glue ─────────────────────────────────────────────────

  def equivDom(v: Val): Val = fstVal(v)
  def equivFun(v: Val): Val = fstVal(sndVal(v))
  def equivContr(v: Val): Val = sndVal(sndVal(v))

  def glue(b: Val, ts: System[Val]): Val = {
    if (ts.contains(Face.eps)) equivDom(ts(Face.eps))
    else VGlue(b, ts)
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

  def unGlue(w: Val, b: Val, equivs: System[Val]): Val = {
    if (equivs.contains(Face.eps)) app(equivFun(equivs(Face.eps)), w)
    else w match {
      case VGlueElem(v, _) => v
      case _ => throw EvalError(s"unGlue: neutral $w")
    }
  }

  def isNeutralGlue(i: Name, equivs: System[Val], u0: Val, ts: System[Val]): Boolean = {
    val equivsi0 = Nominal.face(equivs, Face.dir(i, Dir.Zero))
    ((!equivsi0.contains(Face.eps)) && Val.isNeutral(u0)) ||
    ts.exists { case (alpha, talpha) =>
      (!Nominal.face(equivs, alpha).contains(Face.eps)) && Val.isNeutral(talpha)
    }
  }

  def isNeutralU(i: Name, eqs: System[Val], u0: Val, ts: System[Val]): Boolean = {
    val eqsi0 = Nominal.face(eqs, Face.dir(i, Dir.Zero))
    ((!eqsi0.contains(Face.eps)) && Val.isNeutral(u0)) ||
    ts.exists { case (alpha, talpha) =>
      (!Nominal.face(eqs, alpha).contains(Face.eps)) && Val.isNeutral(talpha)
    }
  }

  def extend(b: Val, q: Val, ts: System[Val]): Val = {
    val i = Nominal.fresh((b, q, ts))
    val ts2 = ts.map { case (alpha, tAlpha) =>
      alpha -> appFormula(app(Nominal.face(sndVal(q), alpha), tAlpha), Formula.Atom(i))
    }
    comp(i, b, fstVal(q), ts2)
  }

  def compGlue(i: Name, a: Val, equivs: System[Val], wi0: Val, ws: System[Val]): Val = {
    val ai1 = Nominal.face(a, Face.dir(i, Dir.One))
    val vs = ws.map { case (alpha, wAlpha) =>
      alpha -> unGlue(wAlpha, Nominal.face(a, alpha), Nominal.face(equivs, alpha))
    }
    val vsi1 = Nominal.face(vs, Face.dir(i, Dir.One))
    val vi0 = unGlue(wi0, Nominal.face(a, Face.dir(i, Dir.Zero)),
                      Nominal.face(equivs, Face.dir(i, Dir.Zero)))
    val vi1p = comp(i, a, vi0, vs)
    val equivsI1 = Nominal.face(equivs, Face.dir(i, Dir.One))
    val equivs2 = equivs.filter { case (alpha, _) => !alpha.contains(i) }

    val us2 = equivs2.map { case (gamma, equivG) =>
      gamma -> fill(i, equivDom(equivG), Nominal.face(wi0, gamma), Nominal.face(ws, gamma))
    }
    val usi12 = equivs2.map { case (gamma, equivG) =>
      gamma -> comp(i, equivDom(equivG), Nominal.face(wi0, gamma), Nominal.face(ws, gamma))
    }

    val ls2 = equivs2.map { case (gamma, equivG) =>
      gamma -> pathComp(i, Nominal.face(a, gamma), Nominal.face(vi0, gamma),
        app(equivFun(equivG), us2(gamma)), Nominal.face(vs, gamma))
    }

    val fibersys: System[Val] = {
      val common = usi12.keySet.intersect(ls2.keySet)
      common.map(k => k -> VPair(usi12(k), ls2(k))).toMap
    }

    val wsi1 = Nominal.face(ws, Face.dir(i, Dir.One))

    val fibersys2 = equivsI1.map { case (gamma, equivG) =>
      val fibsgamma: System[Val] = {
        val wsi1g = Nominal.face(wsi1, gamma)
        val vsi1g = Nominal.face(vsi1, gamma)
        val common = wsi1g.keySet.intersect(vsi1g.keySet)
        common.map(k => k -> VPair(wsi1g(k), Val.constPath(vsi1g(k)))).toMap
      }
      gamma -> extend(
        mkFiberType(Nominal.face(ai1, gamma), Nominal.face(vi1p, gamma), equivG),
        app(equivContr(equivG), Nominal.face(vi1p, gamma)),
        SystemOps.unionSystem(fibsgamma, Nominal.face(fibersys, gamma)))
    }

    val vi1 = compConstLine(ai1, vi1p,
      SystemOps.unionSystem(
        fibersys2.map { case (gamma, v) => gamma -> sndVal(v) },
        vsi1.map { case (gamma, v) => gamma -> Val.constPath(v) }))

    val usi1 = fibersys2.map { case (gamma, v) => gamma -> fstVal(v) }

    glueElem(vi1, usi1)
  }

  def mkFiberType(a: Val, x: Val, equiv: Val): Val = {
    val ta = Term.Var("a")
    val tx = Term.Var("x")
    val ty = Term.Var("y")
    val tf = Term.Var("f")
    val tt = Term.Var("t")
    val env = Environment.updateAll(
      List(("a", a), ("x", x), ("f", equivFun(equiv)), ("t", equivDom(equiv))),
      Environment.empty)
    eval(Term.Sigma(Term.Lam("y", tt, Term.PathP(Term.PLam(Name("_"), ta), tx, Term.App(tf, ty)))), env)
  }

  def pathComp(i: Name, a: Val, u0: Val, u2: Val, us: System[Val]): Val = {
    val j = Nominal.fresh((Formula.Atom(i), a, us, u0, u2))
    VPLam(j, comp(i, a, u0,
      SystemOps.insertsSystem(List((Face.dir(j, Dir.One), u2)), us)))
  }

  // ── Composition in the Universe ──────────────────────────

  def eqFun(eq: Val, v: Val): Val = transNegLine(eq, v)

  def unGlueU(w: Val, b: Val, es: System[Val]): Val = {
    if (es.contains(Face.eps)) eqFun(es(Face.eps), w)
    else w match {
      case VGlueElem(v, _) => v
      case _ => VUnGlueElemU(w, b, es)
    }
  }

  def compUniv(b: Val, es: System[Val]): Val = {
    if (es.contains(Face.eps)) appFormula(es(Face.eps), Formula.Dir(Dir.One))
    else VCompU(b, es)
  }

  def compU(i: Name, a: Val, eqs: System[Val], wi0: Val, ws: System[Val]): Val = {
    val ai1 = Nominal.face(a, Face.dir(i, Dir.One))
    val vs = ws.map { case (alpha, wAlpha) =>
      alpha -> unGlueU(wAlpha, Nominal.face(a, alpha), Nominal.face(eqs, alpha))
    }
    val vsi1 = Nominal.face(vs, Face.dir(i, Dir.One))
    val vi0 = unGlueU(wi0, Nominal.face(a, Face.dir(i, Dir.Zero)),
                       Nominal.face(eqs, Face.dir(i, Dir.Zero)))
    val vi1p = comp(i, a, vi0, vs)
    val eqsI1 = Nominal.face(eqs, Face.dir(i, Dir.One))
    val eqs2 = eqs.filter { case (alpha, _) => !alpha.contains(i) }

    val us2 = eqs2.map { case (gamma, eqG) =>
      gamma -> fill(i, appFormula(eqG, Formula.Dir(Dir.One)), Nominal.face(wi0, gamma), Nominal.face(ws, gamma))
    }
    val usi12 = eqs2.map { case (gamma, eqG) =>
      gamma -> comp(i, appFormula(eqG, Formula.Dir(Dir.One)), Nominal.face(wi0, gamma), Nominal.face(ws, gamma))
    }

    val ls2 = eqs2.map { case (gamma, eqG) =>
      gamma -> pathComp(i, Nominal.face(a, gamma), Nominal.face(vi0, gamma),
        eqFun(eqG, us2(gamma)), Nominal.face(vs, gamma))
    }

    val fibersys: System[(Val, Val)] = {
      val common = usi12.keySet.intersect(ls2.keySet)
      common.map(k => k -> (usi12(k), ls2(k))).toMap
    }

    val wsi1 = Nominal.face(ws, Face.dir(i, Dir.One))

    val fibersys2 = eqsI1.map { case (gamma, eqG) =>
      val fibsgamma: System[(Val, Val)] = {
        val wsi1g = Nominal.face(wsi1, gamma)
        val vsi1g = Nominal.face(vsi1, gamma)
        val common = wsi1g.keySet.intersect(vsi1g.keySet)
        common.map(k => k -> (wsi1g(k), Val.constPath(vsi1g(k)))).toMap
      }
      gamma -> lemEq(eqG, Nominal.face(vi1p, gamma),
        SystemOps.unionSystem(fibsgamma, Nominal.face(fibersys, gamma)))
    }

    val vi1 = compConstLine(ai1, vi1p,
      SystemOps.unionSystem(
        fibersys2.map { case (gamma, (_, p)) => gamma -> p },
        vsi1.map { case (gamma, v) => gamma -> Val.constPath(v) }))

    val usi1 = fibersys2.map { case (gamma, (u, _)) => gamma -> u }

    glueElem(vi1, usi1)
  }

  def lemEq(eq: Val, b: Val, aps: System[(Val, Val)]): (Val, Val) = {
    given Nominal[(Val, Val)] = Nominal.nominalPair[Val, Val]

    val names = Nominal.freshs((eq, b, aps))
    val i = names(0)
    val j = names(1)
    val ta = appFormula(eq, Formula.Dir(Dir.One))

    val p1s = aps.map { case (alpha, (aa, pa)) =>
      val eqaj = appFormula(Nominal.face(eq, alpha), Formula.Atom(j))
      val ba = Nominal.face(b, alpha)
      alpha -> comp(j, eqaj, appFormula(pa, Formula.Atom(i)),
        SystemOps.mkSystem(List(
          (Face.dir(i, Dir.Zero), transFill(j, eqaj, ba)),
          (Face.dir(i, Dir.One), transFillNeg(j, eqaj, aa)))))
    }
    val thetas = aps.map { case (alpha, (aa, pa)) =>
      val eqaj = appFormula(Nominal.face(eq, alpha), Formula.Atom(j))
      val ba = Nominal.face(b, alpha)
      alpha -> fill(j, eqaj, appFormula(pa, Formula.Atom(i)),
        SystemOps.mkSystem(List(
          (Face.dir(i, Dir.Zero), transFill(j, eqaj, ba)),
          (Face.dir(i, Dir.One), transFillNeg(j, eqaj, aa)))))
    }

    val a = comp(i, ta, trans(i, appFormula(eq, Formula.Atom(i)), b), p1s)
    val p1 = fill(i, ta, trans(i, appFormula(eq, Formula.Atom(i)), b), p1s)

    val thetas2 = SystemOps.insertsSystem(
      List(
        (Face.dir(i, Dir.Zero), transFill(j, appFormula(eq, Formula.Atom(j)), b)),
        (Face.dir(i, Dir.One), transFillNeg(j, appFormula(eq, Formula.Atom(j)), a))),
      thetas)

    (a, VPLam(i, compNeg(j, appFormula(eq, Formula.Atom(j)), p1, thetas2)))
  }

  // ── Conversion ───────────────────────────────────────────

  def convert(ns: List[String], u: Val, v: Val): Boolean = {
    if (u == v) return true
    val j = Nominal.fresh((u, v))
    (u, v) match {
      case (Closure(Term.Lam(x, a, u1), e), Closure(Term.Lam(x2, a2, u2), e2)) =>
        val w @ VVar(n, _) = mkVarNice(ns, x, eval(a, e)): @unchecked
        convert(n :: ns, eval(u1, Environment.update((x, w), e)), eval(u2, Environment.update((x2, w), e2)))
      case (Closure(Term.Lam(x, a, u1), e), u2) =>
        val w @ VVar(n, _) = mkVarNice(ns, x, eval(a, e)): @unchecked
        convert(n :: ns, eval(u1, Environment.update((x, w), e)), app(u2, w))
      case (u1, Closure(Term.Lam(x, a, u2), e)) =>
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
      case (VPi(u1, v1), VPi(u2, v2)) =>
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
    val ks = ts.keys.toList
    allCompatible(ks).forall { case (alpha, beta) =>
      convert(ns,
        Nominal.face(ts(alpha), Face.minus(beta, alpha)),
        Nominal.face(ts(beta), Face.minus(alpha, beta)))
    }
  }

  // ── Normalization ────────────────────────────────────────

  def normal(ns: List[String], v: Val): Val = v match {
    case VU => VU
    case Closure(Term.Lam(x, t, u1), e) =>
      val w = eval(t, e)
      val vv @ VVar(n, _) = mkVarNice(ns, x, w): @unchecked
      VLam(n, normal(ns, w), normal(n :: ns, eval(u1, Environment.update((x, vv), e))))
    case Closure(t, e) => Closure(t, normalEnv(ns, e))
    case VPi(u1, v1) => VPi(normal(ns, u1), normal(ns, v1))
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
    case _ => v
  }

  def normalEnv(ns: List[String], e: Environment): Environment = {
    Environment.mapEnv(normal(ns, _), normalFormula, e)
  }

  def normalFormula(phi: Formula): Formula = Formula.fromDNF(Formula.dnf(phi))

  def normalSystem(ns: List[String], ts: System[Val]): System[Val] = {
    ts.map { case (k, v) => k -> normal(ns, v) }
  }

  // ── Helpers ──────────────────────────────────────────────

  def mkVarNice(ns: List[String], x: String, ty: Val): Val = {
    val ys = x #:: LazyList.from(0).map(n => x + n.toString)
    val name = ys.find(y => !ns.contains(y)).get
    VVar(name, ty)
  }

  private def allCompatible(fs: List[Face]): List[(Face, Face)] = fs match {
    case Nil     => Nil
    case f :: rest =>
      rest.filter(Face.compatible(f, _)).map(g => (f, g)) ++ allCompatible(rest)
  }
}

case class EvalError(msg: String) extends RuntimeException(msg)
