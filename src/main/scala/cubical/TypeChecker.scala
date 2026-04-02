package cubical

import Val.*
import Branch.{OBranch, PBranch}
import Label.{lookupLabel, labelName}
import Branch.branchName
import Eval.{nominalVal, nominalEnvironment}

case class TEnv(
  names: List[String],
  indent: Int,
  env: Environment,
  verbose: Boolean
)

object TEnv {
  val verboseEnv: TEnv = TEnv(Nil, 0, Environment.empty, verbose = true)
  val silentEnv: TEnv = TEnv(Nil, 0, Environment.empty, verbose = false)
}

object TypeChecker {

  type Typing[A] = TEnv => Either[String, A]

  private def pure[A](a: A): Typing[A] = _ => Right(a)

  private def throwError[A](msg: String): Typing[A] = _ => Left(msg)

  private def asks[A](f: TEnv => A): Typing[A] = tenv => Right(f(tenv))

  private def local[A](f: TEnv => TEnv)(m: Typing[A]): Typing[A] =
    tenv => m(f(tenv))

  private def flatMap[A, B](m: Typing[A])(f: A => Typing[B]): Typing[B] =
    tenv => m(tenv).flatMap(a => f(a)(tenv))

  private def andThen[A, B](m: Typing[A])(next: Typing[B]): Typing[B] =
    tenv => m(tenv).flatMap(_ => next(tenv))

  private def sequence_[A](ms: Iterable[Typing[A]]): Typing[Unit] =
    tenv => {
      var result: Either[String, Unit] = Right(())
      val iter = ms.iterator
      while (result.isRight && iter.hasNext) {
        result = iter.next()(tenv).map(_ => ())
      }
      result
    }

  private def unless(cond: Boolean)(action: Typing[Unit]): Typing[Unit] =
    if (cond) pure(()) else action

  private def unlessM(condM: Typing[Boolean])(action: Typing[Unit]): Typing[Unit] =
    tenv => condM(tenv).flatMap(c => if (c) Right(()) else action(tenv))

  private def trace(s: String): Typing[Unit] =
    tenv => {
      if (tenv.verbose) println(s)
      Right(())
    }

  // ============================================================
  // Running computations
  // ============================================================

  def runTyping[A](tenv: TEnv, t: Typing[A]): Either[String, A] = t(tenv)

  def runDecls(tenv: TEnv, d: Declarations): Either[String, TEnv] =
    runTyping(tenv, andThen(checkDecls(d))(pure(addDecls(d, tenv))))

  def runDeclss(tenv: TEnv, ds: List[Declarations]): (Option[String], TEnv) = ds match {
    case Nil => (None, tenv)
    case d :: rest =>
      runDecls(tenv, d) match {
        case Right(tenv2) => runDeclss(tenv2, rest)
        case Left(s) => (Some(s), tenv)
      }
  }

  def runInfer(tenv: TEnv, e: Term): Either[String, Val] =
    runTyping(tenv, infer(e))

  // ============================================================
  // Environment modifiers
  // ============================================================

  private def addTypeVal(xv: (Ident, Val), tenv: TEnv): TEnv = {
    val (x, a) = xv
    val w = Eval.mkVarNice(tenv.names, x, a)
    val n = w match { case VVar(n, _) => n; case _ => x }
    TEnv(
      n :: tenv.names,
      tenv.indent,
      Environment.update((x, w), tenv.env),
      tenv.verbose
    )
  }

  private def addSub(iphi: (Name, Formula), tenv: TEnv): TEnv =
    tenv.copy(env = Environment.substitute(iphi, tenv.env))

  private def addSubs(iphis: List[(Name, Formula)], tenv: TEnv): TEnv =
    iphis.foldRight(tenv)((iphi, t) => addSub(iphi, t))

  private def addType(xa: (Ident, Term), tenv: TEnv): TEnv = {
    val (x, a) = xa
    addTypeVal((x, Eval.eval(a, tenv.env)), tenv)
  }

  private def addBranch(nvs: List[(Ident, Val)], nu: Environment, tenv: TEnv): TEnv = {
    val newNames = nvs.collect { case (_, VVar(n, _)) => n }
    TEnv(
      newNames ++ tenv.names,
      tenv.indent,
      Environment.updateAll(nvs, tenv.env),
      tenv.verbose
    )
  }

  private def addDecls(d: Declarations, tenv: TEnv): TEnv =
    tenv.copy(env = Environment.addDecl(d, tenv.env))

  private def addTele(xas: Telescope, tenv: TEnv): TEnv =
    xas.foldLeft(tenv)((t, xa) => addType(xa, t))

  private def faceEnv(alpha: Face, tenv: TEnv): TEnv =
    tenv.copy(env = Nominal.face(tenv.env, alpha))

  // ============================================================
  // Utility functions
  // ============================================================

  private def getLblType(c: LIdent, v: Val): Typing[(Telescope, Environment)] = _ => v match {
    case Val.Closure(Term.Sum(_, _, cas), r) =>
      lookupLabel(c, cas) match {
        case Some(as) => Right((as, r))
        case None => Left(s"getLblType: $c in $cas")
      }
    case Val.Closure(Term.HSum(_, _, cas), r) =>
      lookupLabel(c, cas) match {
        case Some(as) => Right((as, r))
        case None => Left(s"getLblType: $c in $cas")
      }
    case _ => Left(s"expected a data type for the constructor $c but got $v")
  }

  private def mkVars(ns: List[String], tele: Telescope, nu: Environment): List[(Ident, Val)] = tele match {
    case Nil => Nil
    case (x, a) :: xas =>
      val w = Eval.mkVarNice(ns, x, Eval.eval(a, nu))
      val n = w match { case VVar(n, _) => n; case _ => x }
      (x, w) :: mkVars(n :: ns, xas, Environment.update((x, w), nu))
  }

  private def convertM(u: Val, v: Val): Typing[Boolean] =
    tenv => Right(Eval.convert(tenv.names, u, v))

  private def evalTyping(t: Term): Typing[Val] =
    tenv => Right(Eval.eval(t, tenv.env))

  // ============================================================
  // The bidirectional type checker
  // ============================================================

  def check(a: Val, t: Term): Typing[Unit] = tenv => (a, t) match {
    case (_, Term.Undef(_, _)) => Right(())

    case (_, Term.Hole(l)) =>
      val e = Environment.contextOfEnv(tenv.env).reverse.mkString("\n")
      val ns = tenv.names
      if (tenv.verbose) {
        println(s"\nHole at $l:\n\n$e${"—" * 80}\n${Eval.normal(ns, a)}\n")
      }
      Right(())

    case (_, Term.Con(c, es)) =>
      flatMap(getLblType(c, a)) { case (bs, nu) =>
        checks(bs, nu, es)
      }(tenv)

    case (VU, Term.Pi(f)) => checkFam(f)(tenv)

    case (VU, Term.Sigma(f)) => checkFam(f)(tenv)

    case (VU, Term.Sum(_, _, bs)) =>
      sequence_(bs.map {
        case Label.OLabel(_, tele) => checkTele(tele)
        case Label.PLabel(_, _, _, _) =>
          throwError(s"check: no path constructor allowed in $t")
      })(tenv)

    case (VU, Term.HSum(_, _, bs)) =>
      sequence_(bs.map {
        case Label.OLabel(_, tele) => checkTele(tele)
        case Label.PLabel(_, tele, is, ts) =>
          (tenv2: TEnv) => {
            checkTele(tele)(tenv2).flatMap { _ =>
              val rho = tenv2.env
              val domNames = SystemOps.domain(ts).map(_.value)
              if (!domNames.forall(n => is.exists(_.value == n))) {
                Left("names in path label system")
              } else {
                val freshCheck = is.foldLeft[Either[String, Unit]](Right(())) { (acc, i) =>
                  acc.flatMap(_ => checkFresh(i)(tenv2))
                }
                freshCheck.flatMap { _ =>
                  val iis = is.map(i => (i, Formula.Atom(i)))
                  val tenv3 = addSubs(iis, addTele(tele, tenv2))
                  checkSystemWith(ts, (alpha: Face, talpha: Term) =>
                    local((te: TEnv) => faceEnv(alpha, te))(check(Val.Closure(t, rho), talpha))
                  )(tenv3).flatMap { _ =>
                    val rho2 = tenv3.env
                    checkCompSystem(Eval.evalSystem(rho2, ts))(tenv3)
                  }
                }
              }
            }
          }
      })(tenv)

    case (VPi(va, f), Term.Split(_, _, ty, ces)) if isSumOrHSum(va) =>
      val (cas, nu) = extractSumLabels(va)
      for {
        _ <- check(VU, ty)(tenv)
        rho = tenv.env
        isEq <- convertM(a, Eval.eval(ty, rho))(tenv)
        _ <- if (!isEq) Left("check: split annotations") else Right(())
        _ <- if (cas.map(labelName) == ces.map(branchName))
               sequence_(ces.zip(cas).map { case (brc, lbl) =>
                 checkBranch((lbl, nu), f, brc, Val.Closure(t, rho), va)
               })(tenv)
             else Left("case branches does not match the data type")
      } yield ()

    case (VPi(a2, f), Term.Lam(x, a2Ter, body)) =>
      for {
        _ <- check(VU, a2Ter)(tenv)
        ns = tenv.names
        rho = tenv.env
        isEq <- convertM(a2, Eval.eval(a2Ter, rho))(tenv)
        _ <- if (!isEq) Left(
          s"check: lam types don't match\nlambda type annotation: $a2Ter\n" +
          s"domain of Pi: $a2\nnormal form of type: ${Eval.normal(ns, a2)}")
             else Right(())
        varVal = Eval.mkVarNice(ns, x, a2)
        _ <- check(Eval.app(f, varVal), body)(addTypeVal((x, a2), tenv))
      } yield ()

    case (VSigma(a2, f), Term.Pair(t1, t2)) =>
      for {
        _ <- check(a2, t1)(tenv)
        v <- evalTyping(t1)(tenv)
        _ <- check(Eval.app(f, v), t2)(tenv)
      } yield ()

    case (_, Term.Where(e, d)) =>
      for {
        _ <- local((te: TEnv) => te.copy(indent = te.indent + 2))(checkDecls(d))(tenv)
        _ <- local((te: TEnv) => addDecls(d, te))(check(a, e))(tenv)
      } yield ()

    case (VU, Term.PathP(a2, e0, e1)) =>
      for {
        endpoints <- checkPLam(Val.constPath(VU), a2)(tenv)
        (a0, a1) = endpoints
        _ <- check(a0, e0)(tenv)
        _ <- check(a1, e1)(tenv)
      } yield ()

    case (VPathP(p, a0, a1), Term.PLam(_, e)) =>
      for {
        endpoints <- checkPLam(p, t)(tenv)
        (u0, u1) = endpoints
        ns = tenv.names
        _ <- if (Eval.convert(ns, a0, u0) && Eval.convert(ns, a1, u1)) Right(())
             else Left(s"path endpoints don't match for $e, got ($u0, $u1), but expected ($a0, $a1)")
      } yield ()

    case (VU, Term.Glue(a2, ts)) =>
      for {
        _ <- check(VU, a2)(tenv)
        rho = tenv.env
        _ <- checkGlue(Eval.eval(a2, rho), ts)(tenv)
      } yield ()

    case (VGlue(va2, ts), Term.GlueElem(u, us)) =>
      for {
        _ <- check(va2, u)(tenv)
        vu <- evalTyping(u)(tenv)
        _ <- checkGlueElem(vu, ts, us)(tenv)
      } yield ()

    case (VCompU(va2, ves), Term.GlueElem(u, us)) =>
      for {
        _ <- check(va2, u)(tenv)
        vu <- evalTyping(u)(tenv)
        _ <- checkGlueElemU(vu, ves, us)(tenv)
      } yield ()

    case (VU, Term.Id(a2, a0, a1)) =>
      for {
        _ <- check(VU, a2)(tenv)
        va <- evalTyping(a2)(tenv)
        _ <- check(va, a0)(tenv)
        _ <- check(va, a1)(tenv)
      } yield ()

    case (VId(va, va0, va1), Term.IdPair(w, ts)) =>
      for {
        _ <- check(VPathP(Val.constPath(va), va0, va1), w)(tenv)
        vw <- evalTyping(w)(tenv)
        _ <- checkSystemWith(ts, (alpha: Face, tAlpha: Term) =>
          local((te: TEnv) => faceEnv(alpha, te)) { tenv2 =>
            for {
              _ <- check(Nominal.face(va, alpha), tAlpha)(tenv2)
              vtAlpha <- evalTyping(tAlpha)(tenv2)
              isEq <- convertM(Nominal.face(vw, alpha), Val.constPath(vtAlpha))(tenv2)
              _ <- if (!isEq) Left("malformed eqC") else Right(())
            } yield ()
          }
        )(tenv)
        rho = tenv.env
        _ <- checkCompSystem(Eval.evalSystem(rho, ts))(tenv)
      } yield ()

    case _ =>
      for {
        v <- infer(t)(tenv)
        isEq <- convertM(v, a)(tenv)
        _ <- if (!isEq) Left(s"check conv:\n$v\n/=\n$a") else Right(())
      } yield ()
  }

  private def isSumOrHSum(v: Val): Boolean = v match {
    case Val.Closure(Term.Sum(_, _, _), _) => true
    case Val.Closure(Term.HSum(_, _, _), _) => true
    case _ => false
  }

  private def extractSumLabels(v: Val): (List[Label], Environment) = v match {
    case Val.Closure(Term.Sum(_, _, cs), r) => (cs, r)
    case Val.Closure(Term.HSum(_, _, cs), r) => (cs, r)
    case _ => (Nil, Environment.empty)
  }

  def checkDecls(d: Declarations): Typing[Unit] = tenv => d match {
    case Declarations.MutualDecls(_, Nil) => Right(())
    case Declarations.MutualDecls(l, ds) =>
      val idents = Declarations.declIdents(ds)
      val tele = Declarations.declTelescope(ds)
      val ters = Declarations.declTerms(ds)
      val ind = tenv.indent
      trace(" " * ind + "Checking: " + idents.mkString(" "))(tenv).flatMap { _ =>
        checkTele(tele)(tenv).flatMap { _ =>
          val tenv2 = addDecls(Declarations.MutualDecls(l, ds), tenv)
          checks(tele, tenv2.env, ters)(tenv2)
        }
      }
    case Declarations.OpaqueDecl(_) => Right(())
    case Declarations.TransparentDecl(_) => Right(())
    case Declarations.TransparentAllDecl => Right(())
  }

  def checkTele(tele: Telescope): Typing[Unit] = tenv => tele match {
    case Nil => Right(())
    case (x, a) :: xas =>
      check(VU, a)(tenv).flatMap { _ =>
        checkTele(xas)(addType((x, a), tenv))
      }
  }

  private def checkFam(f: Term): Typing[Unit] = tenv => f match {
    case Term.Lam(x, a, b) =>
      check(VU, a)(tenv).flatMap { _ =>
        check(VU, b)(addType((x, a), tenv))
      }
    case x => Left(s"checkFam: $x")
  }

  private def checkCompSystem(vus: System[Val]): Typing[Unit] = tenv => {
    val ns = tenv.names
    if (Eval.isCompSystem(ns, vus)) Right(())
    else Left(s"Incompatible system ${SystemOps.showSystemVal(vus)}")
  }

  private def checkSystemsWith[A, B, C](
    us: System[A],
    vs: System[B],
    f: (Face, A, B) => Typing[C]
  ): Typing[Unit] = tenv => {
    val common = us.keySet.intersect(vs.keySet)
    var result: Either[String, Unit] = Right(())
    val iter = common.iterator
    while (result.isRight && iter.hasNext) {
      val key = iter.next()
      result = f(key, us(key), vs(key))(tenv).map(_ => ())
    }
    result
  }

  private def checkSystemWith[A, B](
    us: System[A],
    f: (Face, A) => Typing[B]
  ): Typing[Unit] = tenv => {
    var result: Either[String, Unit] = Right(())
    val iter = us.iterator
    while (result.isRight && iter.hasNext) {
      val (key, value) = iter.next()
      result = f(key, value)(tenv).map(_ => ())
    }
    result
  }

  private def checkGlueElem(vu: Val, ts: System[Val], us: System[Term]): Typing[Unit] = tenv => {
    if (ts.keySet != us.keySet) {
      Left(s"Keys don't match in $ts and $us")
    } else {
      val rho = tenv.env
      checkSystemsWith(ts, us, (alpha: Face, vt: Val, u: Term) =>
        local((te: TEnv) => faceEnv(alpha, te))(check(Eval.equivDom(vt), u))
      )(tenv).flatMap { _ =>
        val vus = Eval.evalSystem(rho, us)
        checkSystemsWith(ts, vus, (alpha: Face, vt: Val, vAlpha: Val) =>
          unlessM(convertM(Eval.app(Eval.equivFun(vt), vAlpha), Nominal.face(vu, alpha)))(
            throwError(s"Image of glue component $vAlpha doesn't match $vu")
          )
        )(tenv).flatMap { _ =>
          checkCompSystem(vus)(tenv)
        }
      }
    }
  }

  private def checkGlueElemU(vu: Val, ves: System[Val], us: System[Term]): Typing[Unit] = tenv => {
    if (ves.keySet != us.keySet) {
      Left(s"Keys don't match in $ves and $us")
    } else {
      val rho = tenv.env
      checkSystemsWith(ves, us, (alpha: Face, ve: Val, u: Term) =>
        local((te: TEnv) => faceEnv(alpha, te))(
          check(Eval.appFormula(ve, Formula.Dir(Dir.One)), u)
        )
      )(tenv).flatMap { _ =>
        val vus = Eval.evalSystem(rho, us)
        checkSystemsWith(ves, vus, (alpha: Face, ve: Val, vAlpha: Val) =>
          unlessM(convertM(Eval.eqFun(ve, vAlpha), Nominal.face(vu, alpha)))(
            throwError(s"Transport of glueElem (for compU) component $vAlpha doesn't match $vu")
          )
        )(tenv).flatMap { _ =>
          checkCompSystem(vus)(tenv)
        }
      }
    }
  }

  private def checkGlue(va: Val, ts: System[Term]): Typing[Unit] = tenv => {
    checkSystemWith(ts, (alpha: Face, tAlpha: Term) =>
      checkEquiv(Nominal.face(va, alpha), tAlpha)
    )(tenv).flatMap { _ =>
      val rho = tenv.env
      checkCompSystem(Eval.evalSystem(rho, ts))(tenv)
    }
  }

  private def mkIso(vb: Val): Val = {
    val List(a, b, f, g, x, y) = List("a", "b", "f", "g", "x", "y").map(Term.Var(_))
    val rho = Environment.update(("b", vb), Environment.empty)
    Eval.eval(
      Term.Sigma(Term.Lam("a", Term.U,
        Term.Sigma(Term.Lam("f", Term.Pi(Term.Lam("_", a, b)),
          Term.Sigma(Term.Lam("g", Term.Pi(Term.Lam("_", b, a)),
            Term.Sigma(Term.Lam("s", Term.Pi(Term.Lam("y", b,
              Term.PathP(Term.PLam(Name("_"), b), Term.App(f, Term.App(g, y)), y))),
              Term.Pi(Term.Lam("x", a,
                Term.PathP(Term.PLam(Name("_"), a), Term.App(g, Term.App(f, x)), x))))))))))),
      rho
    )
  }

  private def mkEquiv(va: Val): Val = {
    val List(a, f, x, y, s, t2, z) = List("a", "f", "x", "y", "s", "t", "z").map(Term.Var(_))
    val rho = Environment.update(("a", va), Environment.empty)
    val fib = Term.Sigma(Term.Lam("y", t2, Term.PathP(Term.PLam(Name("_"), a), x, Term.App(f, y))))
    val iscontrfib = Term.Sigma(Term.Lam("s", fib,
      Term.Pi(Term.Lam("z", fib, Term.PathP(Term.PLam(Name("_"), fib), s, z)))))
    Eval.eval(
      Term.Sigma(Term.Lam("t", Term.U,
        Term.Sigma(Term.Lam("f", Term.Pi(Term.Lam("_", t2, a)),
          Term.Pi(Term.Lam("x", a, iscontrfib)))))),
      rho
    )
  }

  private def checkEquiv(va: Val, equiv: Term): Typing[Unit] =
    check(mkEquiv(va), equiv)

  private def checkIso(vb: Val, iso: Term): Typing[Unit] =
    check(mkIso(vb), iso)

  private def checkBranch(
    labelEnv: (Label, Environment),
    f: Val,
    brc: Branch,
    g: Val,
    va: Val
  ): Typing[Unit] = tenv => (labelEnv._1, brc) match {
    case (Label.OLabel(_, tele), OBranch(c, ns, e)) =>
      val nu = labelEnv._2
      val ns2 = tenv.names
      val us = mkVars(ns2, tele, nu).map(_._2)
      check(Eval.app(f, VCon(c, us)), e)(
        addBranch(ns.zip(us), nu, tenv)
      )

    case (Label.PLabel(_, tele, is, ts), PBranch(c, ns, js, e)) =>
      val nu = labelEnv._2
      val ns2 = tenv.names
      val us = mkVars(ns2, tele, nu)
      val vus = us.map(_._2)
      val js2 = js.map(Formula.Atom(_))
      val nuUpd = Environment.substituteAll(
        is.zip(js2),
        Environment.updateAll(us, nu)
      )
      val vts = Eval.evalSystem(nuUpd, ts)
      val vgts = vts.map { case (alpha, vt) =>
        alpha -> Eval.app(Nominal.face(g, alpha), vt)
      }
      val tenv2 = addSubs(js.map(j => (j, Formula.Atom(j))), addBranch(ns.zip(vus), nu, tenv))
      check(Eval.app(f, VPCon(c, va, vus, js2)), e)(tenv2).flatMap { _ =>
        evalTyping(e)(tenv2).flatMap { ve =>
          val veBorder: System[Val] = Nominal.border(ve, vts)
          val allMatch = (veBorder.keySet ++ vgts.keySet).forall { k =>
            (veBorder.get(k), vgts.get(k)) match {
              case (Some(v1), Some(v2)) => Eval.convert(tenv2.names, v1, v2)
              case _ => false
            }
          }
          if (!allMatch) Left(
            s"Faces in branch for $c don't match:\n" +
            s"got\n${SystemOps.showSystemVal(veBorder)}\nbut expected\n${SystemOps.showSystemVal(vgts)}")
          else Right(())
        }
      }

    case _ => Left(s"checkBranch: mismatched label and branch")
  }

  private def checkFormula(phi: Formula): Typing[Unit] = tenv => {
    val rho = tenv.env
    val dom = Environment.domainEnv(rho)
    if (Nominal.support(phi).forall(n => dom.contains(n))) Right(())
    else Left(s"checkFormula: $phi")
  }

  private def checkFresh(i: Name): Typing[Unit] = tenv => {
    val rho = tenv.env
    if (Nominal.support(rho).contains(i))
      Left(s"$i is already declared")
    else Right(())
  }

  private def checkPLam(v: Val, t: Term): Typing[(Val, Val)] = tenv => t match {
    case Term.PLam(i, a) =>
      val rho = tenv.env
      val tenv2 = addSub((i, Formula.Atom(i)), tenv)
      check(Eval.appFormula(v, Formula.Atom(i)), a)(tenv2).map { _ =>
        val v0 = Eval.eval(a, Environment.substitute((i, Formula.Dir(Dir.Zero)), rho))
        val v1 = Eval.eval(a, Environment.substitute((i, Formula.Dir(Dir.One)), rho))
        (v0, v1)
      }
    case _ =>
      infer(t)(tenv).flatMap { vt =>
        vt match {
          case VPathP(a, a0, a1) =>
            val isEq = Eval.convert(tenv.names, a, v)
            if (!isEq) Left(s"checkPLam\n$v\n/=\n$a")
            else Right((a0, a1))
          case _ => Left(s"$vt is not a path")
        }
      }
  }

  private def checkPLamSystem(t0: Term, va: Val, ps: System[Term]): Typing[System[Val]] = tenv => {
    val rho = tenv.env
    var result: Either[String, Map[Face, Val]] = Right(Map.empty)
    val iter = ps.iterator
    while (result.isRight && iter.hasNext) {
      val (alpha, pAlpha) = iter.next()
      val tenvAlpha = faceEnv(alpha, tenv)
      val entry = for {
        endpoints <- checkPLam(Nominal.face(va, alpha), pAlpha)(tenvAlpha)
        (a0, a1) = endpoints
        rhoAlpha = tenvAlpha.env
        isEq <- convertM(a0, Eval.eval(t0, rhoAlpha))(tenvAlpha)
        _ <- if (!isEq) Left(
          s"Incompatible system, component\n $pAlpha\n" +
          s"incompatible with\n $t0\na0 = $a0\nt0alpha = ${Eval.eval(t0, rhoAlpha)}\nva = $va")
             else Right(())
      } yield a1
      result = entry.flatMap(v => result.map(_ + (alpha -> v)))
    }
    result.flatMap { v =>
      checkCompSystem(Eval.evalSystem(rho, ps))(tenv).map(_ => v)
    }
  }

  private def checks(tele: Telescope, nu: Environment, es: List[Term]): Typing[Unit] =
    tenv => (tele, es) match {
      case (Nil, Nil) => Right(())
      case ((x, a) :: xas, e :: rest) =>
        check(Eval.eval(a, nu), e)(tenv).flatMap { _ =>
          evalTyping(e)(tenv).flatMap { v =>
            checks(xas, Environment.update((x, v), nu), rest)(tenv)
          }
        }
      case _ => Left("checks: incorrect number of arguments")
    }

  def infer(e: Term): Typing[Val] = tenv => e match {
    case Term.U => Right(VU)

    case Term.Var(n) => Right(Eval.lookType(n, tenv.env))

    case Term.App(t, u) =>
      infer(t)(tenv).flatMap {
        case VPi(a, f) =>
          check(a, u)(tenv).flatMap { _ =>
            evalTyping(u)(tenv).map(v => Eval.app(f, v))
          }
        case c => Left(s"$c is not a product")
      }

    case Term.Fst(t) =>
      infer(t)(tenv).flatMap {
        case VSigma(a, _) => Right(a)
        case c => Left(s"$c is not a sigma-type")
      }

    case Term.Snd(t) =>
      infer(t)(tenv).flatMap {
        case VSigma(_, f) =>
          evalTyping(t)(tenv).map(v => Eval.app(f, Eval.fstVal(v)))
        case c => Left(s"$c is not a sigma-type")
      }

    case Term.Where(t, d) =>
      checkDecls(d)(tenv).flatMap { _ =>
        infer(t)(addDecls(d, tenv))
      }

    case Term.UnGlueElem(e2, _) =>
      infer(e2)(tenv).flatMap {
        case VGlue(a, _) => Right(a)
        case t2 => Left(s"$t2 is not a Glue")
      }

    case Term.AppFormula(e2, phi) =>
      checkFormula(phi)(tenv).flatMap { _ =>
        infer(e2)(tenv).flatMap {
          case VPathP(a, _, _) => Right(Eval.appFormula(a, phi))
          case _ => Left(s"$e2 is not a path")
        }
      }

    case Term.Comp(a, t0, ps) =>
      for {
        endpoints <- checkPLam(Val.constPath(VU), a)(tenv)
        (va0, va1) = endpoints
        va <- evalTyping(a)(tenv)
        _ <- check(va0, t0)(tenv)
        _ <- checkPLamSystem(t0, va, ps)(tenv)
      } yield va1

    case Term.HComp(a, u0, us) =>
      for {
        _ <- check(VU, a)(tenv)
        va <- evalTyping(a)(tenv)
        _ <- check(va, u0)(tenv)
        _ <- checkPLamSystem(u0, Val.constPath(va), us)(tenv)
      } yield va

    case Term.Fill(a, t0, ps) =>
      for {
        endpoints <- checkPLam(Val.constPath(VU), a)(tenv)
        (va0, _) = endpoints
        va <- evalTyping(a)(tenv)
        _ <- check(va0, t0)(tenv)
        _ <- checkPLamSystem(t0, va, ps)(tenv)
        vt <- evalTyping(t0)(tenv)
        rho = tenv.env
        vps = Eval.evalSystem(rho, ps)
      } yield VPathP(va, vt, Eval.compLine(va, vt, vps))

    case Term.PCon(c, a, es, phis) =>
      for {
        _ <- check(VU, a)(tenv)
        va <- evalTyping(a)(tenv)
        bsNu <- getLblType(c, va)(tenv)
        (bs, nu) = bsNu
        _ <- checks(bs, nu, es)(tenv)
        _ <- sequence_(phis.map(checkFormula))(tenv)
      } yield va

    case Term.IdJ(a, u, c, d, x, p) =>
      for {
        _ <- check(VU, a)(tenv)
        va <- evalTyping(a)(tenv)
        _ <- check(va, u)(tenv)
        vu <- evalTyping(u)(tenv)
        refu = VIdPair(Val.constPath(vu), SystemOps.mkSystem(List((Face.eps, vu))))
        rho = tenv.env
        ctype = Eval.eval(Term.Pi(Term.Lam("z", a, Term.Pi(Term.Lam("_", Term.Id(a, u, Term.Var("z")), Term.U)))), rho)
        _ <- check(ctype, c)(tenv)
        vc <- evalTyping(c)(tenv)
        _ <- check(Eval.app(Eval.app(vc, vu), refu), d)(tenv)
        _ <- check(va, x)(tenv)
        vx <- evalTyping(x)(tenv)
        _ <- check(VId(va, vu, vx), p)(tenv)
        vp <- evalTyping(p)(tenv)
      } yield Eval.app(Eval.app(vc, vx), vp)

    case _ => Left(s"infer $e")
  }
}
