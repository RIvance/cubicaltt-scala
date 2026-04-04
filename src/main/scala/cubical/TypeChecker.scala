package cubical

import Val.*
import Branch.{OrdinaryBranch, PathBranch}
import Label.{lookupLabel, labelName}
import Branch.branchName
import Eval.{nominalVal, nominalEnvironment}

case class TypeCheckError(msg: String) extends RuntimeException(msg)

case class TypeEnv(
  names: List[String],
  indent: Int,
  env: Environment,
  verbose: Boolean
)

object TypeEnv {
  val verboseEnv: TypeEnv = TypeEnv(Nil, 0, Environment.empty, verbose = true)
  val silentEnv: TypeEnv = TypeEnv(Nil, 0, Environment.empty, verbose = false)
}

object TypeChecker {

  /**
   * Public API — run declarations or infer a type, catching `TypeCheckError`.
   *
   * These are the entry points used by `Main` and tests.  They convert internal
   * exceptions into `Either[String, _]` / `Option[String]` so callers can handle
   * errors without catching exceptions.
   */
  def runDecls(typeEnv: TypeEnv, d: Declarations): Either[String, TypeEnv] =
    try {
      checkDecls(d, typeEnv)
      Right(addDecls(d, typeEnv))
    } catch {
      case e: TypeCheckError => Left(e.msg)
    }

  def runDeclss(typeEnv: TypeEnv, declsList: List[Declarations]): (Option[String], TypeEnv) = declsList match {
    case Nil => (None, typeEnv)
    case d :: rest =>
      runDecls(typeEnv, d) match {
        case Right(typeEnv2) => runDeclss(typeEnv2, rest)
        case Left(s)         => (Some(s), typeEnv)
      }
  }

  def runInfer(typeEnv: TypeEnv, term: Term): Either[String, Type] =
    try Right(infer(term, typeEnv))
    catch { case e: TypeCheckError => Left(e.msg) }

  /**
   * Environment modifiers — extend a `TypeEnv` with a new binding or substitution.
   *
   * These helpers thread the environment through the bidirectional checker without
   * exposing `Environment` mutation directly.  Each modifier is pure and returns a
   * fresh `TypeEnv`.
   */
  private[cubical] def addTypeVal(identValPair: (Ident, Type), typeEnv: TypeEnv): TypeEnv = {
    val (x, valType) = identValPair
    val freshVar = Eval.mkVarNice(typeEnv.names, x, valType)
    val n = freshVar match { case VVar(n, _) => n; case _ => x }
    TypeEnv(
      n :: typeEnv.names,
      typeEnv.indent,
      Environment.update((x, freshVar), typeEnv.env),
      typeEnv.verbose
    )
  }

  private def addSub(nameFormulaPair: (Name, Formula), typeEnv: TypeEnv): TypeEnv =
    typeEnv.copy(env = Environment.substitute(nameFormulaPair, typeEnv.env))

  private def addSubs(nameFormulaPairs: List[(Name, Formula)], typeEnv: TypeEnv): TypeEnv =
    nameFormulaPairs.foldRight(typeEnv)((nameFormulaPair, t) => addSub(nameFormulaPair, t))

  private[cubical] def addType(identTermPair: (Ident, Term), typeEnv: TypeEnv): TypeEnv = {
    val (x, termTy) = identTermPair
    addTypeVal((x, Eval.eval(termTy, typeEnv.env)), typeEnv)
  }

  private def addBranch(branchVars: List[(Ident, Val)], labelEnv: Environment, typeEnv: TypeEnv): TypeEnv = {
    val newNames = branchVars.collect { case (_, VVar(n, _)) => n }
    TypeEnv(
      newNames ++ typeEnv.names,
      typeEnv.indent,
      Environment.updateAll(branchVars, typeEnv.env),
      typeEnv.verbose
    )
  }

  private def addDecls(decls: Declarations, typeEnv: TypeEnv): TypeEnv =
    typeEnv.copy(env = Environment.addDecl(decls, typeEnv.env))

  private def addTele(tele: Telescope, typeEnv: TypeEnv): TypeEnv =
    tele.foldLeft(typeEnv)((t, entry) => addType(entry, t))

  private def faceEnv(alpha: Face, typeEnv: TypeEnv): TypeEnv =
    typeEnv.copy(env = Nominal.face(typeEnv.env, alpha))

  /**
   * Utility functions — small helpers shared by `check` and `infer`.
   *
   * `getLabelType` — look up the telescope of a constructor label in a sum type.
   *
   * `mkVars` — generate fresh `VVar` values for each entry in a telescope, extending
   * the name list and closure environment as it goes.
   */
  private def getLabelType(label: LabelIdent, dataTypeVal: Val, typeEnv: TypeEnv): (Telescope, Environment) = dataTypeVal match {
    case Val.Closure(Term.Sum(_, _, labels), closureEnv) =>
      lookupLabel(label, labels) match {
        case Some(tele) => (tele, closureEnv)
        case None     => throw TypeCheckError(s"getLabelType: $label in $labels")
      }
    case Val.Closure(Term.HSum(_, _, labels), closureEnv) =>
      lookupLabel(label, labels) match {
        case Some(tele) => (tele, closureEnv)
        case None     => throw TypeCheckError(s"getLabelType: $label in $labels")
      }
    case _ => throw TypeCheckError(s"expected a data type for the constructor $label but got $dataTypeVal")
  }

  private def mkVars(usedNames: List[String], tele: Telescope, closureEnv: Environment): List[(Ident, Val)] = tele match {
    case Nil => Nil
    case (x, a) :: teleRest =>
      val freshVar = Eval.mkVarNice(usedNames, x, Eval.eval(a, closureEnv))
      val freshName = freshVar match { case VVar(n, _) => n; case _ => x }
      (x, freshVar) :: mkVars(freshName :: usedNames, teleRest, Environment.update((x, freshVar), closureEnv))
  }

  /**
   * The bidirectional type checker.
   *
   * {{{
   *   Γ ⊢ t ⇐ A    (check: `t` is checked against known type `A`)
   *   Γ ⊢ t ⇒ A    (infer: type `A` is synthesised for `t`)
   *
   *   Γ ⊢ t ⇒ B    Γ ⊢ A =_β B
   *   ──────────────────────────── (⇒-to-⇐ subsumption)
   *   Γ ⊢ t ⇐ A
   * }}}
   *
   * `check` pattern-matches on pairs `(A, t)`; when no specialised rule applies
   * it falls back to synthesis followed by conversion (`Γ ⊢ t ⇒ B`, then `A =_β B`).
   * `infer` handles introductions and eliminators that carry enough annotation to
   * determine the type without a hint.
   */
  def check(expectedType: Type, t: Term, typeEnv: TypeEnv): Unit = (expectedType, t) match {
    case (_, Term.Undef(_, _)) => ()

    case (_, Term.Hole(l)) =>
      val e = Environment.contextOfEnv(typeEnv.env).reverse.mkString("\n")
      val ns = typeEnv.names
      if (typeEnv.verbose) {
        println(s"\nHole at $l:\n\n$e${"—" * 80}\n${Eval.normal(ns, expectedType)}\n")
      }

    case (_, Term.Con(label, args)) =>
      val (labelTele, closureEnv) = getLabelType(label, expectedType, typeEnv)
      checks(labelTele, closureEnv, args, typeEnv)

    case (VU, Term.Pi(_, codomain)) => checkFam(codomain, typeEnv)

    case (VU, Term.Sigma(famTerm)) => checkFam(famTerm, typeEnv)

    case (VU, Term.Sum(_, _, caseBranches)) =>
      caseBranches.foreach {
        case Label.OrdinaryLabel(_, tele) => checkTele(tele, typeEnv)
        case Label.PathLabel(_, _, _, _) =>
          throw TypeCheckError(s"check: no path constructor allowed in $t")
      }

    case (VU, Term.HSum(_, _, caseBranches)) =>
      caseBranches.foreach {
        case Label.OrdinaryLabel(_, tele) => checkTele(tele, typeEnv)
        case Label.PathLabel(_, tele, is, ts) =>
          checkTele(tele, typeEnv)
          val rho = typeEnv.env
          val domNames = SystemOps.domain(ts).map(_.value)
          if (!domNames.forall(n => is.exists(_.value == n)))
            throw TypeCheckError("names in path label system")
          is.foreach(i => checkFresh(i, typeEnv))
          val dimAtomPairs = is.map(i => (i, Formula.Atom(i)))
          val typeEnv3 = addSubs(dimAtomPairs, addTele(tele, typeEnv))
          checkSystemWith(ts, (alpha: Face, talpha: Term) =>
            check(Val.Closure(t, rho), talpha, faceEnv(alpha, typeEnv3))
          , typeEnv3)
          val rho2 = typeEnv3.env
          checkCompSystem(Eval.evalSystem(rho2, ts), typeEnv3)
      }

    case (VPi(_, valA, codomain), Term.Split(_, _, ty, caseBranches)) if isSumOrHSum(valA) =>
      val (labels, closureEnv) = extractSumLabels(valA)
      check(VU, ty, typeEnv)
      val rho = typeEnv.env
      if (!Eval.convert(typeEnv.names, expectedType, Eval.eval(ty, rho)))
        throw TypeCheckError("check: split annotations")
      if (labels.map(labelName) != caseBranches.map(branchName))
        throw TypeCheckError("case branches does not match the data type")
      caseBranches.zip(labels).foreach { case (branch, lbl) =>
        checkBranch((lbl, closureEnv), codomain, branch, Val.Closure(t, rho), valA, typeEnv)
      }

    case (VPi(_, valA2, f), Term.Lam(_, x, a2Ter, body)) =>
      check(VU, a2Ter, typeEnv)
      val ns = typeEnv.names
      val rho = typeEnv.env
      if (!Eval.convert(ns, valA2, Eval.eval(a2Ter, rho)))
        throw TypeCheckError(
          s"check: lam types don't match\nlambda type annotation: $a2Ter\n" +
          s"domain of Pi: $valA2\nnormal form of type: ${Eval.normal(ns, valA2)}"
        )
      val varVal = Eval.mkVarNice(ns, x, valA2)
      check(Eval.app(f, varVal), body, addTypeVal((x, valA2), typeEnv))

    case (VSigma(valA2, f), Term.Pair(t1, t2)) =>
      check(valA2, t1, typeEnv)
      val v = Eval.eval(t1, typeEnv.env)
      check(Eval.app(f, v), t2, typeEnv)

    case (_, Term.Where(e, d)) =>
      checkDecls(d, typeEnv.copy(indent = typeEnv.indent + 2))
      check(expectedType, e, addDecls(d, typeEnv))

    case (VU, Term.PathP(a2, e0, e1)) =>
      val (a0, a1) = checkPLam(Val.constPath(VU), a2, typeEnv)
      check(a0, e0, typeEnv)
      check(a1, e1, typeEnv)

    case (VPathP(p, a0, a1), Term.PLam(_, e)) =>
      val (u0, u1) = checkPLam(p, t, typeEnv)
      val ns = typeEnv.names
      if (!Eval.convert(ns, a0, u0) || !Eval.convert(ns, a1, u1))
        throw TypeCheckError(s"path endpoints don't match for $e, got ($u0, $u1), but expected ($a0, $a1)")

    case (VU, Term.Glue(a2, ts)) =>
      check(VU, a2, typeEnv)
      val rho = typeEnv.env
      checkGlue(Eval.eval(a2, rho), ts, typeEnv)

    case (VGlue(valA2, ts), Term.GlueElem(u, us)) =>
      check(valA2, u, typeEnv)
      val evaledU = Eval.eval(u, typeEnv.env)
      checkGlueElem(evaledU, ts, us, typeEnv)

    case (VCompU(valA2, ves), Term.GlueElem(u, us)) =>
      check(valA2, u, typeEnv)
      val evaledU = Eval.eval(u, typeEnv.env)
      checkGlueElemU(evaledU, ves, us, typeEnv)

    case (VU, Term.Id(a2, a0, a1)) =>
      check(VU, a2, typeEnv)
      val valA = Eval.eval(a2, typeEnv.env)
      check(valA, a0, typeEnv)
      check(valA, a1, typeEnv)

    case (VId(valA, valA0, valA1), Term.IdPair(w, ts)) =>
      check(VPathP(Val.constPath(valA), valA0, valA1), w, typeEnv)
      val evaledWitness = Eval.eval(w, typeEnv.env)
      checkSystemWith(ts, (alpha: Face, tAlpha: Term) => {
        val typeEnv2 = faceEnv(alpha, typeEnv)
        check(Nominal.face(valA, alpha), tAlpha, typeEnv2)
        val vtAlpha = Eval.eval(tAlpha, typeEnv2.env)
        if (!Eval.convert(typeEnv2.names, Nominal.face(evaledWitness, alpha), Val.constPath(vtAlpha)))
          throw TypeCheckError("malformed eqC")
      }, typeEnv)
      val rho = typeEnv.env
      checkCompSystem(Eval.evalSystem(rho, ts), typeEnv)

    case _ =>
      val v = infer(t, typeEnv)
      if (!Eval.convert(typeEnv.names, v, expectedType))
        throw TypeCheckError(s"check conv:\n$v\n/=\n$expectedType")
  }

  private def isSumOrHSum(v: Val): Boolean = v match {
    case Val.Closure(Term.Sum(_, _, _), _)  => true
    case Val.Closure(Term.HSum(_, _, _), _) => true
    case _                                  => false
  }

  private def extractSumLabels(sumVal: Val): (List[Label], Environment) = sumVal match {
    case Val.Closure(Term.Sum(_, _, labels), closureEnv)  => (labels, closureEnv)
    case Val.Closure(Term.HSum(_, _, labels), closureEnv) => (labels, closureEnv)
    case _                                                 => (Nil, Environment.empty)
  }

  def checkDecls(d: Declarations, typeEnv: TypeEnv): Unit = d match {
    case Declarations.MutualDecls(_, Nil) => ()
    case Declarations.MutualDecls(loc, declPairs) =>
      val idents = Declarations.declIdents(declPairs)
      val tele   = Declarations.declTelescope(declPairs)
      val ters   = Declarations.declTerms(declPairs)
      val indentLevel = typeEnv.indent
      if (typeEnv.verbose) println(" " * indentLevel + "Checking: " + idents.mkString(" "))
      checkTele(tele, typeEnv)
      val typeEnv2 = addDecls(Declarations.MutualDecls(loc, declPairs), typeEnv)
      checks(tele, typeEnv2.env, ters, typeEnv2)
    case Declarations.OpaqueDecl(_)       => ()
    case Declarations.TransparentDecl(_)  => ()
    case Declarations.TransparentAllDecl  => ()
  }

  def checkTele(tele: Telescope, typeEnv: TypeEnv): Unit = tele match {
    case Nil => ()
    case (x, a) :: teleRest =>
      check(VU, a, typeEnv)
      checkTele(teleRest, addType((x, a), typeEnv))
  }

  private def checkFam(famTerm: Term, typeEnv: TypeEnv): Unit = famTerm match {
    case Term.Lam(_, x, a, b) =>
      check(VU, a, typeEnv)
      check(VU, b, addType((x, a), typeEnv))
    case x => throw TypeCheckError(s"checkFam: $x")
  }

  private def checkCompSystem(compSystem: System[Val], typeEnv: TypeEnv): Unit = {
    val ns = typeEnv.names
    if (!Eval.isCompSystem(ns, compSystem))
      throw TypeCheckError(s"Incompatible system ${SystemOps.showSystemVal(compSystem)}")
  }

  private def checkSystemsWith[A, B](
    us: System[A],
    vs: System[B],
    checker: (Face, A, B) => Unit,
    typeEnv: TypeEnv
  ): Unit = {
    val common = us.keySet.intersect(vs.keySet)
    common.foreach { key => checker(key, us(key), vs(key)) }
  }

  private def checkSystemWith[A](
    us: System[A],
    checker: (Face, A) => Unit,
    typeEnv: TypeEnv
  ): Unit =
    us.foreach { case (key, value) => checker(key, value) }

  private def checkGlueElem(evaledU: Val, equivSys: System[Val], elemTerms: System[Term], typeEnv: TypeEnv): Unit = {
    if (equivSys.keySet != elemTerms.keySet)
      throw TypeCheckError(s"Keys don't match in $equivSys and $elemTerms")
    val rho = typeEnv.env
    checkSystemsWith(equivSys, elemTerms, (alpha: Face, equivComponent: Val, u: Term) =>
      check(Eval.equivDom(equivComponent), u, faceEnv(alpha, typeEnv))
    , typeEnv)
    val evaledElems = Eval.evalSystem(rho, elemTerms)
    checkSystemsWith(equivSys, evaledElems, (alpha: Face, equivComponent: Val, vAlpha: Val) => {
      if (!Eval.convert(typeEnv.names, Eval.app(Eval.equivFun(equivComponent), vAlpha), Nominal.face(evaledU, alpha)))
        throw TypeCheckError(s"Image of glue component $vAlpha doesn't match $evaledU")
    }, typeEnv)
    checkCompSystem(evaledElems, typeEnv)
  }

  private def checkGlueElemU(evaledU: Val, equivPaths: System[Val], elemTerms: System[Term], typeEnv: TypeEnv): Unit = {
    if (equivPaths.keySet != elemTerms.keySet)
      throw TypeCheckError(s"Keys don't match in $equivPaths and $elemTerms")
    val rho = typeEnv.env
    checkSystemsWith(equivPaths, elemTerms, (alpha: Face, eqComponent: Val, u: Term) =>
      check(Eval.appFormula(eqComponent, Formula.Dir(Dir.One)), u, faceEnv(alpha, typeEnv))
    , typeEnv)
    val evaledElems = Eval.evalSystem(rho, elemTerms)
    checkSystemsWith(equivPaths, evaledElems, (alpha: Face, eqComponent: Val, vAlpha: Val) => {
      if (!Eval.convert(typeEnv.names, Eval.eqFun(eqComponent, vAlpha), Nominal.face(evaledU, alpha)))
        throw TypeCheckError(s"Transport of glueElem (for compU) component $vAlpha doesn't match $evaledU")
    }, typeEnv)
    checkCompSystem(evaledElems, typeEnv)
  }

  private def checkGlue(valA: Type, equivTerms: System[Term], typeEnv: TypeEnv): Unit = {
    checkSystemWith(equivTerms, (alpha: Face, tAlpha: Term) =>
      checkEquiv(Nominal.face(valA, alpha), tAlpha, typeEnv), typeEnv)
    val rho = typeEnv.env
    checkCompSystem(Eval.evalSystem(rho, equivTerms), typeEnv)
  }

  private def mkIso(vb: Type): Type = {
    val List(a, b, f, g, x, y) = List("a", "b", "f", "g", "x", "y").map(Term.Var(_))
    val rho = Environment.update(("b", vb), Environment.empty)
    Eval.eval(
      Term.Sigma(Term.Lam(Icity.Explicit, "a", Term.U,
        Term.Sigma(Term.Lam(Icity.Explicit, "f", Term.Pi(Icity.Explicit, Term.Lam(Icity.Explicit, "_", a, b)),
          Term.Sigma(Term.Lam(Icity.Explicit, "g", Term.Pi(Icity.Explicit, Term.Lam(Icity.Explicit, "_", b, a)),
            Term.Sigma(Term.Lam(Icity.Explicit, "s", Term.Pi(Icity.Explicit, Term.Lam(Icity.Explicit, "y", b,
              Term.PathP(Term.PLam(Name("_"), b), Term.App(Icity.Explicit, f, Term.App(Icity.Explicit, g, y)), y))),
              Term.Pi(Icity.Explicit, Term.Lam(Icity.Explicit, "x", a,
                Term.PathP(Term.PLam(Name("_"), a), Term.App(Icity.Explicit, g, Term.App(Icity.Explicit, f, x)), x))))))))))),
      rho
    )
  }

  private def mkEquiv(valA: Type): Type = {
    val List(a, f, x, y, s, typeVar, z) = List("a", "f", "x", "y", "s", "t", "z").map(Term.Var(_))
    val rho = Environment.update(("a", valA), Environment.empty)
    val fiberType = Term.Sigma(Term.Lam(Icity.Explicit, "y", typeVar, Term.PathP(Term.PLam(Name("_"), a), x, Term.App(Icity.Explicit, f, y))))
    val isContrFiber = Term.Sigma(Term.Lam(Icity.Explicit, "s", fiberType,
      Term.Pi(Icity.Explicit, Term.Lam(Icity.Explicit, "z", fiberType, Term.PathP(Term.PLam(Name("_"), fiberType), s, z)))))
    Eval.eval(
      Term.Sigma(Term.Lam(Icity.Explicit, "t", Term.U,
        Term.Sigma(Term.Lam(Icity.Explicit, "f", Term.Pi(Icity.Explicit, Term.Lam(Icity.Explicit, "_", typeVar, a)),
          Term.Pi(Icity.Explicit, Term.Lam(Icity.Explicit, "x", a, isContrFiber)))))),
      rho
    )
  }

  private def checkEquiv(valA: Type, equiv: Term, typeEnv: TypeEnv): Unit =
    check(mkEquiv(valA), equiv, typeEnv)

  private def checkIso(vb: Type, iso: Term, typeEnv: TypeEnv): Unit =
    check(mkIso(vb), iso, typeEnv)

  private def checkBranch(
    labelEnv: (Label, Environment),
    codomain: Val,
    branch: Branch,
    splitClosure: Val,
    valA: Type,
    typeEnv: TypeEnv
  ): Unit = (labelEnv._1, branch) match {
    case (Label.OrdinaryLabel(_, tele), OrdinaryBranch(c, ns, e)) =>
      val labelEnvClosure = labelEnv._2
      val currentNames = typeEnv.names
      val constructorArgs = mkVars(currentNames, tele, labelEnvClosure).map(_._2)
      check(Eval.app(codomain, VCon(c, constructorArgs)), e, addBranch(ns.zip(constructorArgs), labelEnvClosure, typeEnv))

    case (Label.PathLabel(_, tele, is, ts), PathBranch(c, ns, js, e)) =>
      val labelEnvClosure = labelEnv._2
      val currentNames = typeEnv.names
      val us = mkVars(currentNames, tele, labelEnvClosure)
      val freshVarVals = us.map(_._2)
      val dimFormulas = js.map(Formula.Atom(_))
      val updatedEnv = Environment.substituteAll(
        is.zip(dimFormulas),
        Environment.updateAll(us, labelEnvClosure)
      )
      val evaledFaceSystem = Eval.evalSystem(updatedEnv, ts)
      val branchFaceVals = evaledFaceSystem.map { case (alpha, faceVal) =>
        alpha -> Eval.app(Nominal.face(splitClosure, alpha), faceVal)
      }
      val typeEnv2 = addSubs(js.map(j => (j, Formula.Atom(j))), addBranch(ns.zip(freshVarVals), labelEnvClosure, typeEnv))
      check(Eval.app(codomain, VPCon(c, valA, freshVarVals, dimFormulas)), e, typeEnv2)
      val evaledBranchBody = Eval.eval(e, typeEnv2.env)
      val evaledBranchBodyBorder: System[Val] = Nominal.border(evaledBranchBody, evaledFaceSystem)
      val allMatch = (evaledBranchBodyBorder.keySet ++ branchFaceVals.keySet).forall { k =>
        (evaledBranchBodyBorder.get(k), branchFaceVals.get(k)) match {
          case (Some(v1), Some(v2)) => Eval.convert(typeEnv2.names, v1, v2)
          case _                    => false
        }
      }
      if (!allMatch)
        throw TypeCheckError(
          s"Faces in branch for $c don't match:\n" +
          s"got\n${SystemOps.showSystemVal(evaledBranchBodyBorder)}\nbut expected\n${SystemOps.showSystemVal(branchFaceVals)}"
        )

    case _ => throw TypeCheckError(s"checkBranch: mismatched label and branch")
  }

  private def checkFormula(phi: Formula, typeEnv: TypeEnv): Unit = {
    val rho = typeEnv.env
    val dom = Environment.domainEnv(rho)
    if (!Nominal.support(phi).forall(n => dom.contains(n)))
      throw TypeCheckError(s"checkFormula: $phi")
  }

  private def checkFresh(i: Name, typeEnv: TypeEnv): Unit = {
    val rho = typeEnv.env
    if (Nominal.support(rho).contains(i))
      throw TypeCheckError(s"$i is already declared")
  }

  private def checkPLam(pathTy: Val, t: Term, typeEnv: TypeEnv): (Val, Val) = t match {
    case Term.PLam(i, a) =>
      val rho = typeEnv.env
      val typeEnv2 = addSub((i, Formula.Atom(i)), typeEnv)
      check(Eval.appFormula(pathTy, Formula.Atom(i)), a, typeEnv2)
      val v0 = Eval.eval(a, Environment.substitute((i, Formula.Dir(Dir.Zero)), rho))
      val v1 = Eval.eval(a, Environment.substitute((i, Formula.Dir(Dir.One)), rho))
      (v0, v1)
    case _ =>
      infer(t, typeEnv) match {
        case VPathP(a, a0, a1) =>
          if (!Eval.convert(typeEnv.names, a, pathTy))
            throw TypeCheckError(s"checkPLam\n$pathTy\n/=\n$a")
          (a0, a1)
        case inferredType => throw TypeCheckError(s"$inferredType is not a path")
      }
  }

  private def checkPLamSystem(t0: Term, valA: Type, ps: System[Term], typeEnv: TypeEnv): System[Val] = {
    val rho = typeEnv.env
    val result = ps.map { case (alpha, pathAtFace) =>
      val typeEnvAtFace = faceEnv(alpha, typeEnv)
      val (a0, a1) = checkPLam(Nominal.face(valA, alpha), pathAtFace, typeEnvAtFace)
      val envAtFace = typeEnvAtFace.env
      if (!Eval.convert(typeEnvAtFace.names, a0, Eval.eval(t0, envAtFace)))
        throw TypeCheckError(
          s"Incompatible system, component\n $pathAtFace\n" +
          s"incompatible with\n $t0\na0 = $a0\nt0alpha = ${Eval.eval(t0, envAtFace)}\nva = $valA"
        )
      alpha -> a1
    }
    checkCompSystem(Eval.evalSystem(rho, ps), typeEnv)
    result
  }

  private def checks(tele: Telescope, closureEnv: Environment, constructorArgs: List[Term], typeEnv: TypeEnv): Unit =
    (tele, constructorArgs) match {
      case (Nil, Nil) => ()
      case ((x, argType) :: teleRest, argTerm :: rest) =>
        check(Eval.eval(argType, closureEnv), argTerm, typeEnv)
        val v = Eval.eval(argTerm, typeEnv.env)
        checks(teleRest, Environment.update((x, v), closureEnv), rest, typeEnv)
      case _ => throw TypeCheckError("checks: incorrect number of arguments")
    }

  def infer(term: Term, typeEnv: TypeEnv): Type = term match {
    case Term.U => VU

    case Term.Var(n) => Eval.lookupType(n, typeEnv.env)

    case Term.App(_, t, u) =>
      infer(t, typeEnv) match {
        case VPi(_, a, f) =>
          check(a, u, typeEnv)
          Eval.app(f, Eval.eval(u, typeEnv.env))
        case inferredType => throw TypeCheckError(s"$inferredType is not a product")
      }

    case Term.Fst(t) =>
      infer(t, typeEnv) match {
        case VSigma(a, _) => a
        case inferredType => throw TypeCheckError(s"$inferredType is not a sigma-type")
      }

    case Term.Snd(t) =>
      infer(t, typeEnv) match {
        case VSigma(_, f) => Eval.app(f, Eval.fstVal(Eval.eval(t, typeEnv.env)))
        case inferredType => throw TypeCheckError(s"$inferredType is not a sigma-type")
      }

    case Term.Where(t, d) =>
      checkDecls(d, typeEnv)
      infer(t, addDecls(d, typeEnv))

    case Term.UnGlueElem(e2, _) =>
      infer(e2, typeEnv) match {
        case VGlue(a, _) => a
        case inferredType => throw TypeCheckError(s"$inferredType is not a Glue")
      }

    case Term.AppFormula(e2, phi) =>
      checkFormula(phi, typeEnv)
      infer(e2, typeEnv) match {
        case VPathP(a, _, _) => Eval.appFormula(a, phi)
        case _ => throw TypeCheckError(s"$e2 is not a path")
      }

    case Term.Comp(a, t0, ps) =>
      val (_, rightEndpoint) = checkPLam(Val.constPath(VU), a, typeEnv)
      val valA = Eval.eval(a, typeEnv.env)
      check(Eval.appFormula(valA, Formula.Dir(Dir.Zero)), t0, typeEnv)
      checkPLamSystem(t0, valA, ps, typeEnv)
      rightEndpoint

    case Term.HComp(a, u0, us) =>
      check(VU, a, typeEnv)
      val valA = Eval.eval(a, typeEnv.env)
      check(valA, u0, typeEnv)
      checkPLamSystem(u0, Val.constPath(valA), us, typeEnv)
      valA

    case Term.Fill(a, t0, ps) =>
      val (leftEndpoint, _) = checkPLam(Val.constPath(VU), a, typeEnv)
      val valA = Eval.eval(a, typeEnv.env)
      check(leftEndpoint, t0, typeEnv)
      checkPLamSystem(t0, valA, ps, typeEnv)
      val evaledBase = Eval.eval(t0, typeEnv.env)
      val rho = typeEnv.env
      val evaledPathSys = Eval.evalSystem(rho, ps)
      VPathP(valA, evaledBase, Eval.compLine(valA, evaledBase, evaledPathSys))

    case Term.PCon(c, a, es, phis) =>
      check(VU, a, typeEnv)
      val valA = Eval.eval(a, typeEnv.env)
      val (labelTele, closureEnv) = getLabelType(c, valA, typeEnv)
      checks(labelTele, closureEnv, es, typeEnv)
      phis.foreach(checkFormula(_, typeEnv))
      valA

    case Term.IdJ(a, u, c, d, x, p) =>
      check(VU, a, typeEnv)
      val valA = Eval.eval(a, typeEnv.env)
      check(valA, u, typeEnv)
      val evaledLeft = Eval.eval(u, typeEnv.env)
      val reflElement = VIdPair(Val.constPath(evaledLeft), SystemOps.mkSystem(List((Face.eps, evaledLeft))))
      val rho = typeEnv.env
      val ctype = Eval.eval(Term.Pi(Icity.Explicit, Term.Lam(Icity.Explicit, "z", a, Term.Pi(Icity.Explicit, Term.Lam(Icity.Explicit, "_", Term.Id(a, u, Term.Var("z")), Term.U)))), rho)
      check(ctype, c, typeEnv)
      val evaledMotive = Eval.eval(c, typeEnv.env)
      check(Eval.app(Eval.app(evaledMotive, evaledLeft), reflElement), d, typeEnv)
      check(valA, x, typeEnv)
      val evaledRight = Eval.eval(x, typeEnv.env)
      check(VId(valA, evaledLeft, evaledRight), p, typeEnv)
      val evaledPath = Eval.eval(p, typeEnv.env)
      Eval.app(Eval.app(evaledMotive, evaledRight), evaledPath)

    case _ => throw TypeCheckError(s"infer $term")
  }
}
