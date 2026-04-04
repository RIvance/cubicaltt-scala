package cubical

/**
 * Bidirectional elaborator that wraps the core `TypeChecker` with
 * metavariable-aware implicit argument insertion.
 *
 * The elaboration pipeline is:
 *
 * {{{
 *   Raw Term  ──parse+resolve──▶  Term (with Icity annotations)
 *             ──elaborate──▶      Term (metas solved, implicit args inserted)
 *             ──zonk──▶           Term (no remaining Meta nodes)
 *             ──TypeChecker──▶    ✓ well-typed
 * }}}
 *
 * Key invariant: `MetaContext` is threaded immutably through every call.
 * The elaborator never mutates global state — it returns an updated
 * `MetaContext` alongside its results, just like `TypeEnv` is threaded
 * through the core checker.
 *
 * The elaborator intercepts two specific situations:
 *   1. **Implicit application insertion** (`infer` on `App`):
 *      When the head of an application has type `{x : A} → B`, the
 *      elaborator inserts a fresh meta `?n : A` before the explicit arg.
 *   2. **Implicit lambda insertion** (`check` against `VPi(Implicit, …)`):
 *      When checking a term against an implicit Π-type and the term is
 *      not already an implicit λ, wrap it in `λ {x} → …` with a fresh meta.
 *
 * For all other cases the elaborator delegates to `TypeChecker.check` /
 * `TypeChecker.infer` unchanged.
 */
object Elaborator {

  /**
    * Infer the type of `term` under `typeEnv`, threading `metaCtx`.
    *
    * Application terms are handled by `inferApp` (spine-based).
    * All other terms delegate to `TypeChecker.infer`.
    */
  def infer(term: Term, typeEnv: TypeEnv, metaCtx: MetaContext): (Term, Val, MetaContext) = term match {
    case Term.App(_, _, _) if needsElaboration(term, typeEnv) =>
      inferApp(term, typeEnv, metaCtx)

    case _ =>
      val (preElabTerm, mc1) = preElaborate(term, typeEnv, metaCtx)
      val inferredType = TypeChecker.infer(preElabTerm, typeEnv)
      (preElabTerm, inferredType, mc1)
  }

  /**
    * Spine-based inference for application terms.
    *
    * Decomposes `f a₁ … aₙ` into `(f, [a₁, …, aₙ])`, infers the head,
    * and processes each argument in order — inserting implicit metas before
    * explicit arguments, and peeling Π-layers for each.
    */
  private def inferApp(term: Term, typeEnv: TypeEnv, metaCtx: MetaContext): (Term, Val, MetaContext) = {
    val (head, spine) = Term.unApps(term)
    val (elaboratedHead, headType, metaCtx1) = infer(head, typeEnv, metaCtx)

    spine.foldLeft((elaboratedHead, headType, metaCtx1)) {
      case ((currentHead, currentType, metaCtx), (Icity.Explicit, argTerm)) =>
        val (insertedHead, exposedType, metaCtx1) = insertImplicits(currentHead, currentType, metaCtx)
        MetaContext.force(metaCtx1, exposedType) match {
          case Val.VPi(Icity.Explicit, domain, codomain) =>
            val solvedDomain = MetaContext.force(metaCtx1, domain)
            val (elaboratedArg, metaCtx2) =
              if (MetaContext.containsMeta(metaCtx1, solvedDomain)) {
                val (elabArg, inferredArgType, mc2) = infer(argTerm, typeEnv, metaCtx1)
                val mc3 = Unify.unify(typeEnv.names, solvedDomain, inferredArgType, mc2)
                (elabArg, mc3)
              } else {
                check(solvedDomain, argTerm, typeEnv, metaCtx1)
              }
            val zonkedArg = MetaContext.zonkTerm(metaCtx2, elaboratedArg)
            val argVal = Eval.eval(zonkedArg, typeEnv.env)
            (Term.App(Icity.Explicit, insertedHead, zonkedArg), Eval.app(codomain, argVal), metaCtx2)
          case other =>
            throw TypeCheckError(s"Expected function type, got: $other")
        }

      case ((currentHead, currentType, metaCtx), (Icity.Implicit, argTerm)) =>
        MetaContext.force(metaCtx, currentType) match {
          case Val.VPi(Icity.Implicit, domain, codomain) =>
            val (elaboratedArg, metaCtx1) = check(domain, argTerm, typeEnv, metaCtx)
            val zonkedArg = MetaContext.zonkTerm(metaCtx1, elaboratedArg)
            val argVal = Eval.eval(zonkedArg, typeEnv.env)
            (Term.App(Icity.Implicit, currentHead, zonkedArg), Eval.app(codomain, argVal), metaCtx1)
          case other =>
            throw TypeCheckError(s"Expected implicit function type, got: $other")
        }
    }
  }

  /**
   * Consume leading implicit Π-binders by inserting fresh metas.
   *
   * Given `f : {A : U} → {B : U} → (A → B) → …`, calling
   * `insertImplicits(f, fTy, mc)` produces:
   * {{{
   *   (f {?0} {?1},  (?0 → ?1) → …,  mc')
   * }}}
   * where `?0 : U` and `?1 : U` are fresh unsolved metas.
   */
  private def insertImplicits(
    elaboratedHead: Term,
    headType: Val,
    metaCtx: MetaContext
  ): (Term, Val, MetaContext) = {
    val forced = MetaContext.force(metaCtx, headType)
    forced match {
      case Val.VPi(Icity.Implicit, domain, codomain) =>
        val (metaVal, metaCtx1) = metaCtx.freshMeta(domain)
        val metaTerm = Term.Meta(metaCtx1.nextId - 1)
        val newHead = Term.App(Icity.Implicit, elaboratedHead, metaTerm)
        val resultType = Eval.app(codomain, metaVal)
        insertImplicits(newHead, resultType, metaCtx1)
      case _ =>
        (elaboratedHead, forced, metaCtx)
    }
  }

  /**
    * Check `term` against `expected` type under `typeEnv`, threading `metaCtx`.
    *
    * Returns a pair `(elaboratedTerm, updatedMetaCtx)`.
    *
    * Intercepts three cases before falling through to the core checker:
    *   1. Implicit Π-type + non-implicit-λ term → insert implicit lambda
    *   2. Application terms → delegate to spine-based `checkApp`
    *   3. Everything else → `TypeChecker.check`
    */
  def check(expected: Val, term: Term, typeEnv: TypeEnv, metaCtx: MetaContext): (Term, MetaContext) = {
    val forced = MetaContext.force(metaCtx, expected)
    forced match {
      case Val.VPi(Icity.Implicit, domain, codomain) if !isImplicitLam(term) =>
        val name = "_impl"
        val (metaVal, metaCtx1) = metaCtx.freshMeta(domain)
        val metaTerm = Term.Meta(metaCtx1.nextId - 1)
        val domainTerm = MetaContext.readBackVal(metaCtx1, domain)
        val bodyType = Eval.app(codomain, metaVal)
        val (elaboratedBody, metaCtx2) = check(bodyType, term, typeEnv, metaCtx1)
        (Term.Lam(Icity.Implicit, name, domainTerm, elaboratedBody), metaCtx2)

      case Val.VPi(icity, valA, codomain) =>
        term match {
          case Term.Lam(icity2, x, aTerm, bodyTerm) =>
            val (elabA, metaCtx1) = check(Val.VU, aTerm, typeEnv, metaCtx)
            val zonkedA = MetaContext.zonkTerm(metaCtx1, elabA)
            val evaledA = Eval.eval(zonkedA, typeEnv.env)
            if (!Eval.convert(typeEnv.names, valA, evaledA))
              throw TypeCheckError(
                s"check: lam types don't match\nlambda annotation: $aTerm\ndomain of Pi: $valA"
              )
            val varVal = Eval.mkVarNice(typeEnv.names, x, valA)
            val innerTypeEnv = TypeChecker.addTypeVal((x, valA), typeEnv)
            val bodyType = Eval.app(codomain, varVal)
            val (elabBody, metaCtx2) = check(bodyType, bodyTerm, innerTypeEnv, metaCtx1)
            (Term.Lam(icity2, x, zonkedA, elabBody), metaCtx2)

          case _ =>
            term match {
              case Term.App(_, _, _) if needsElaboration(term, typeEnv) =>
                // Try inferApp+unify first (left-to-right, better for higher-order motives).
                // Fall back to checkApp (backward result-type unification) when inferApp
                // can't check an argument against an unsolved meta domain (e.g. PLam args).
                try {
                  val (elabTerm, inferredType, mc1) = inferApp(term, typeEnv, metaCtx)
                  val mc2 = Unify.unify(typeEnv.names, forced, inferredType, mc1)
                  (MetaContext.zonkTerm(mc2, elabTerm), mc2)
                } catch {
                  case _: TypeCheckError =>
                    checkApp(forced, term, typeEnv, metaCtx)
                }
              case Term.Where(e, decls) =>
                val (newTypeEnv, _, zonkedDecls) = elaborateDecls(decls, typeEnv, MetaContext.empty)
                val (elabE, metaCtx1) = check(forced, e, newTypeEnv, metaCtx)
                val zonkedE = MetaContext.zonkTerm(metaCtx1, elabE)
                (Term.Where(zonkedE, zonkedDecls), metaCtx1)
              case _ if isPurelyInferrable(term) =>
                // For terms whose types are fully determined by inference (Var, App, Fst, Snd, etc.),
                // use infer+unify rather than TypeChecker.check, so that metas embedded inside
                // the expected type (e.g. in closures) are resolved via Unify rather than
                // causing a raw Eval.convert failure.
                val (preElabTerm, mc1) = preElaborate(term, typeEnv, metaCtx)
                val (elaboratedTerm, inferredType, mc2) = infer(preElabTerm, typeEnv, mc1)
                val mc3 = Unify.unify(typeEnv.names, forced, inferredType, mc2)
                (elaboratedTerm, mc3)
              case _ =>
                TypeChecker.check(forced, term, typeEnv)
                (term, metaCtx)
            }
        }

      case Val.VU if term.isInstanceOf[Term.PathP] =>
        val Term.PathP(familyTerm, e0, e1) = term.asInstanceOf[Term.PathP]
        val (elabFamily, metaCtx1) = elaboratePathFamily(familyTerm, typeEnv, metaCtx)
        val zonkedFamily = MetaContext.zonkTerm(metaCtx1, elabFamily)
        val familyVal = Eval.eval(zonkedFamily, typeEnv.env)
        val a0 = Eval.appFormula(familyVal, Formula.Dir(Dir.Zero))
        val a1 = Eval.appFormula(familyVal, Formula.Dir(Dir.One))
        val (elabE0, metaCtx2) = check(a0, e0, typeEnv, metaCtx1)
        val (elabE1, metaCtx3) = check(a1, e1, typeEnv, metaCtx2)
        (Term.PathP(zonkedFamily, elabE0, elabE1), metaCtx3)

      case Val.VPathP(pathFamily, pathA0, pathA1) if term.isInstanceOf[Term.PLam] =>
        val Term.PLam(dimName, body) = term.asInstanceOf[Term.PLam]
        val dimEnv = typeEnv.copy(
          env = Environment.substitute((dimName, Formula.Atom(dimName)), typeEnv.env)
        )
        val bodyType = Eval.appFormula(pathFamily, Formula.Atom(dimName))
        val (elabBody, metaCtx1) = check(bodyType, body, dimEnv, metaCtx)
        val zonkedBody = MetaContext.zonkTerm(metaCtx1, elabBody)
        val u0 = Eval.eval(zonkedBody, Environment.substitute((dimName, Formula.Dir(Dir.Zero)), typeEnv.env))
        val u1 = Eval.eval(zonkedBody, Environment.substitute((dimName, Formula.Dir(Dir.One)), typeEnv.env))
        val forcedA0 = MetaContext.force(metaCtx1, pathA0)
        val forcedA1 = MetaContext.force(metaCtx1, pathA1)
        if (!Eval.convert(typeEnv.names, forcedA0, u0) || !Eval.convert(typeEnv.names, forcedA1, u1))
          throw TypeCheckError(
            s"path endpoints don't match: got ($u0, $u1), expected ($forcedA0, $forcedA1)"
          )
        (Term.PLam(dimName, zonkedBody), metaCtx1)

      case _ => term match {
        case Term.Pi(icity, Term.Lam(icity2, x, a, b)) if forced == Val.VU =>
          val (elabA, metaCtx1) = check(Val.VU, a, typeEnv, metaCtx)
          val zonkedA = MetaContext.zonkTerm(metaCtx1, elabA)
          val innerTypeEnv = TypeChecker.addType((x, zonkedA), typeEnv)
          val (elabB, metaCtx2) = check(Val.VU, b, innerTypeEnv, metaCtx1)
          val zonkedB = MetaContext.zonkTerm(metaCtx2, elabB)
          (Term.Pi(icity, Term.Lam(icity2, x, zonkedA, zonkedB)), metaCtx2)

        case Term.Sigma(Term.Lam(icity2, x, a, b)) if forced == Val.VU =>
          val (elabA, metaCtx1) = check(Val.VU, a, typeEnv, metaCtx)
          val zonkedA = MetaContext.zonkTerm(metaCtx1, elabA)
          val innerTypeEnv = TypeChecker.addType((x, zonkedA), typeEnv)
          val (elabB, metaCtx2) = check(Val.VU, b, innerTypeEnv, metaCtx1)
          val zonkedB = MetaContext.zonkTerm(metaCtx2, elabB)
          (Term.Sigma(Term.Lam(icity2, x, zonkedA, zonkedB)), metaCtx2)

        case Term.Where(e, decls) =>
          val (newTypeEnv, _, zonkedDecls) = elaborateDecls(decls, typeEnv, MetaContext.empty)
          val (elabE, metaCtx1) = check(forced, e, newTypeEnv, metaCtx)
          val zonkedE = MetaContext.zonkTerm(metaCtx1, elabE)
          (Term.Where(zonkedE, zonkedDecls), metaCtx1)

        case Term.App(_, _, _) if needsElaboration(term, typeEnv) =>
          try {
            val (elabTerm, inferredType, mc1) = inferApp(term, typeEnv, metaCtx)
            val mc2 = Unify.unify(typeEnv.names, forced, inferredType, mc1)
            (MetaContext.zonkTerm(mc2, elabTerm), mc2)
          } catch {
            case _: TypeCheckError =>
              checkApp(forced, term, typeEnv, metaCtx)
          }
        case _ =>
          forced match {
            case Val.VMeta(id) =>
              try {
                val (elaboratedTerm, inferredType, metaCtx1) = infer(term, typeEnv, metaCtx)
                val metaCtx2 = Unify.unify(typeEnv.names, forced, inferredType, metaCtx1)
                (elaboratedTerm, metaCtx2)
              } catch {
                case _: TypeCheckError =>
                  throw TypeCheckError(s"Cannot infer type of $term to solve metavariable ?$id")
              }
            case _ =>
              val (preElabTerm, metaCtx1) = preElaborate(term, typeEnv, metaCtx)
              if (isPurelyInferrable(preElabTerm)) {
                val (elaboratedTerm, inferredType, mc2) = infer(preElabTerm, typeEnv, metaCtx1)
                val mc3 = Unify.unify(typeEnv.names, forced, inferredType, mc2)
                (elaboratedTerm, mc3)
              } else {
                TypeChecker.check(forced, preElabTerm, typeEnv)
                (preElabTerm, metaCtx1)
              }
          }
      }
    }
  }

  /**
    * Check an application term against an expected type using spine-based
    * result-first unification.
    *
    * The key idea: instead of processing applications one level at a time
    * (which causes inner calls to `infer` where domains are still unsolved
    * metas), we decompose the entire application spine at once:
    *
    * {{{
    *   constI tt tt : Unit
    *   ─── spine ──▶  (constI, [(Explicit, tt), (Explicit, tt)])
    * }}}
    *
    * Then:
    *   1. Infer the head type (`constI : {A:U} → {B:U} → A → B → A`)
    *   2. Insert implicit metas (`?0:U`, `?1:U`), exposed: `?0 → ?1 → ?0`
    *   3. For each explicit arg, create an arg-placeholder meta and peel
    *      one Π-layer, accumulating `(domain, argTerm, argMeta)` triples
    *   4. Unify the **final result type** with the expected type — this
    *      propagates information backwards, solving domain metas
    *   5. Force each domain and check arguments left-to-right
    *   6. Unify each arg-meta with the actual argument value
    *
    * This ordering ensures that `?0 = Unit` is solved (via the return type)
    * before we ever try to `check(tt, ?0)`.
    */
  private def checkApp(expected: Val, term: Term, typeEnv: TypeEnv, metaCtx: MetaContext): (Term, MetaContext) = {
    val (head, spine) = Term.unApps(term)
    val (elaboratedHead, headType, metaCtx1) = infer(head, typeEnv, metaCtx)

    case class SpineEntry(domain: Val, argTerm: Term, argMeta: Val, icity: Icity)

    // Phase A: Walk the spine, inserting implicit metas before each explicit arg
    //          and peeling Π-layers. Accumulate entries for later checking.
    val (currentHead, currentType, entries, metaCtx2) =
      spine.foldLeft((elaboratedHead, headType, List.empty[SpineEntry], metaCtx1)) {
        case ((head, headType, entries, metaCtx), (Icity.Explicit, argTerm)) =>
          val (insertedHead, exposedType, metaCtx1) = insertImplicits(head, headType, metaCtx)
          MetaContext.force(metaCtx1, exposedType) match {
            case Val.VPi(Icity.Explicit, domain, codomain) =>
              val (argMeta, metaCtx2) = metaCtx1.freshMeta(domain)
              val resultType = Eval.app(codomain, argMeta)
              (insertedHead, resultType, entries :+ SpineEntry(domain, argTerm, argMeta, Icity.Explicit), metaCtx2)
            case other =>
              throw TypeCheckError(s"Expected function type, got: $other")
          }

        case ((head, headType, entries, metaCtx), (Icity.Implicit, argTerm)) =>
          MetaContext.force(metaCtx, headType) match {
            case Val.VPi(Icity.Implicit, domain, codomain) =>
              val (argMeta, metaCtx1) = metaCtx.freshMeta(domain)
              val resultType = Eval.app(codomain, argMeta)
              (head, resultType, entries :+ SpineEntry(domain, argTerm, argMeta, Icity.Implicit), metaCtx1)
            case other =>
              throw TypeCheckError(s"Expected implicit function type, got: $other")
          }
      }

    // Phase B: Unify the final result type with the expected type FIRST.
    //          This backward propagation solves domain metas.
    val metaCtx3 = Unify.unify(typeEnv.names, currentType, expected, metaCtx2)

    // Phase C: Check each argument left-to-right with (now-solved) domains,
    //          and rebuild the application term.
    val (rebuiltTerm, metaCtx4) = entries.foldLeft((currentHead, metaCtx3)) {
      case ((rebuiltTerm, metaCtx), entry) =>
        val solvedDomain = MetaContext.force(metaCtx, entry.domain)
        val (elaboratedArg, metaCtx1) = check(solvedDomain, entry.argTerm, typeEnv, metaCtx)
        val zonkedArg = MetaContext.zonkTerm(metaCtx1, elaboratedArg)
        val argVal = Eval.eval(zonkedArg, typeEnv.env)
        val metaCtx2 = Unify.unify(typeEnv.names, entry.argMeta, argVal, metaCtx1)
        (Term.App(entry.icity, rebuiltTerm, zonkedArg), metaCtx2)
    }

    (rebuiltTerm, metaCtx4)
  }

  private def isImplicitLam(term: Term): Boolean = term match {
    case Term.Lam(Icity.Implicit, _, _, _) => true
    case _ => false
  }

  /**
    * True when an application term involves implicit arguments and therefore
    * needs the elaborator's spine-based `checkApp` instead of the core
    * `TypeChecker.check`.
    *
    * Two conditions trigger elaboration:
    *   1. The spine contains an explicit implicit application `{arg}`
    *   2. The head variable's type starts with `VPi(Implicit, …)`,
    *      meaning the elaborator must insert implicit metas
    */
  private def elaboratePathFamily(familyTerm: Term, typeEnv: TypeEnv, metaCtx: MetaContext): (Term, MetaContext) =
    familyTerm match {
      case Term.PLam(dimName, body) =>
        val dimEnv = typeEnv.copy(
          env = Environment.substitute((dimName, Formula.Atom(dimName)), typeEnv.env)
        )
        val (elabBody, metaCtx1) = check(Val.VU, body, dimEnv, metaCtx)
        (Term.PLam(dimName, elabBody), metaCtx1)
      case Term.App(_, _, _) if needsElaboration(familyTerm, typeEnv) =>
        val (elabFamily, _, metaCtx1) = inferApp(familyTerm, typeEnv, metaCtx)
        (MetaContext.zonkTerm(metaCtx1, elabFamily), metaCtx1)
      case _ =>
        (familyTerm, metaCtx)
    }

  /**
   * Recursively pre-elaborate a term by inserting implicit arguments into all
   * application sub-terms that need them, before the core `TypeChecker` sees
   * the term.
   *
   * This is needed for cubical primitives (`comp`, `fill`, `AppFormula`, etc.)
   * that the Elaborator's `check` method does not directly intercept. Their
   * sub-terms may contain calls to functions with implicit arguments (e.g.
   * `transNeg p y` inside a `comp` base), which the core checker cannot handle.
   *
   * `preElaborate` works in inference mode only: it uses `inferApp` for
   * applications, which is sound because implicit arguments can always be
   * inferred from the explicit argument types.
   */
  private def preElaborate(term: Term, typeEnv: TypeEnv, metaCtx: MetaContext): (Term, MetaContext) = term match {
    case Term.App(_, _, _) if needsElaboration(term, typeEnv) =>
      val (elabTerm, _, mc1) = inferApp(term, typeEnv, metaCtx)
      (MetaContext.zonkTerm(mc1, elabTerm), mc1)

    case Term.App(icity, f, arg) =>
      val (elabF, mc1) = preElaborate(f, typeEnv, metaCtx)
      val (elabArg, mc2) = preElaborate(arg, typeEnv, mc1)
      (Term.App(icity, elabF, elabArg), mc2)

    case Term.PLam(i, body) =>
      val dimEnv = typeEnv.copy(
        env = Environment.substitute((i, Formula.Atom(i)), typeEnv.env)
      )
      val (elabBody, mc1) = preElaborate(body, dimEnv, metaCtx)
      (Term.PLam(i, elabBody), mc1)

    case Term.Comp(ty, base, sys) =>
      val (elabTy, mc0)   = preElaborate(ty, typeEnv, metaCtx)
      val (elabBase, mc1) = preElaborate(base, typeEnv, mc0)
      val (elabSys, mc2)  = preElaborateSystem(sys, typeEnv, mc1)
      (Term.Comp(elabTy, elabBase, elabSys), mc2)

    case Term.Fill(ty, base, sys) =>
      val (elabTy, mc0)   = preElaborate(ty, typeEnv, metaCtx)
      val (elabBase, mc1) = preElaborate(base, typeEnv, mc0)
      val (elabSys, mc2)  = preElaborateSystem(sys, typeEnv, mc1)
      (Term.Fill(elabTy, elabBase, elabSys), mc2)

    case Term.AppFormula(e, phi) =>
      val (elabE, mc1) = preElaborate(e, typeEnv, metaCtx)
      (Term.AppFormula(elabE, phi), mc1)

    case Term.Pair(a, b) =>
      val (elabA, mc1) = preElaborate(a, typeEnv, metaCtx)
      val (elabB, mc2) = preElaborate(b, typeEnv, mc1)
      (Term.Pair(elabA, elabB), mc2)

    case Term.Fst(t) =>
      val (elabT, mc1) = preElaborate(t, typeEnv, metaCtx)
      (Term.Fst(elabT), mc1)

    case Term.Snd(t) =>
      val (elabT, mc1) = preElaborate(t, typeEnv, metaCtx)
      (Term.Snd(elabT), mc1)

    case Term.Lam(icity, x, a, body) =>
      // Extend the environment with the lambda variable so that the body can
      // be pre-elaborated in the correct scope.  Without this, any implicit
      // application inside the body that refers to `x` (e.g. `Path x y` inside
      // `\(y:A) → Path x y`) would fail because `x` is not in scope during
      // pre-elaboration.
      val domainVal = try Eval.eval(a, typeEnv.env) catch { case _: Exception => Val.VU }
      val innerTypeEnv = TypeChecker.addTypeVal((x, domainVal), typeEnv)
      val (elabBody, mc1) = preElaborate(body, innerTypeEnv, metaCtx)
      (Term.Lam(icity, x, a, elabBody), mc1)

    case Term.Pi(icity, Term.Lam(icity2, x, a, b)) =>
      val (elabA, mc1) = preElaborate(a, typeEnv, metaCtx)
      val domainVal = try Eval.eval(a, typeEnv.env) catch { case _: Exception => Val.VU }
      val innerTypeEnv = TypeChecker.addTypeVal((x, domainVal), typeEnv)
      val (elabB, mc2) = preElaborate(b, innerTypeEnv, mc1)
      (Term.Pi(icity, Term.Lam(icity2, x, elabA, elabB)), mc2)

    case Term.Sigma(Term.Lam(icity2, x, a, b)) =>
      val (elabA, mc1) = preElaborate(a, typeEnv, metaCtx)
      val domainVal = try Eval.eval(a, typeEnv.env) catch { case _: Exception => Val.VU }
      val innerTypeEnv = TypeChecker.addTypeVal((x, domainVal), typeEnv)
      val (elabB, mc2) = preElaborate(b, innerTypeEnv, mc1)
      (Term.Sigma(Term.Lam(icity2, x, elabA, elabB)), mc2)

    case _ => (term, metaCtx)
  }

  private def preElaborateSystem(
    sys: System[Term],
    typeEnv: TypeEnv,
    metaCtx: MetaContext
  ): (System[Term], MetaContext) =
    sys.foldLeft((Map.empty[Face, Term], metaCtx)) {
      case ((accSys, mc), (face, t)) =>
        val faceEnv = TypeChecker.faceEnv(face, typeEnv)
        val (elabT, mc1) = preElaborate(t, faceEnv, mc)
        (accSys + (face -> elabT), mc1)
    }

   private def needsElaboration(term: Term, typeEnv: TypeEnv): Boolean = {
     val (head, spine) = Term.unApps(term)
     if (spine.exists(_._1 == Icity.Implicit)) return true
     head match {
       case Term.Var(name) =>
         try {
           Eval.lookupType(name, typeEnv.env) match {
             case Val.VPi(Icity.Implicit, _, _) => true
             case _ => false
           }
         } catch {
           case _: Exception => false
         }
       case _ => false
     }
   }

  private def isPurelyInferrable(term: Term): Boolean = term match {
    case Term.Var(_) | Term.U | Term.App(_, _, _) | Term.Fst(_) | Term.Snd(_)
       | Term.AppFormula(_, _) | Term.Comp(_, _, _) | Term.Fill(_, _, _)
       | Term.HComp(_, _, _) | Term.UnGlueElem(_, _) | Term.PCon(_, _, _, _)
       | Term.IdJ(_, _, _, _, _, _) => true
    case _ => false
  }

  /**
   * Elaborate a block of mutual declarations, returning the updated environment,
   * the final metavariable context, and the zonked (meta-substituted) declarations.
   */
   def elaborateDecls(decls: Declarations, typeEnv: TypeEnv, metaCtx: MetaContext): (TypeEnv, MetaContext, Declarations) = decls match {
     case Declarations.MutualDecls(loc, declPairs) =>
       val tempTypeEnv = typeEnv.copy(env = Environment.addDecl(decls, typeEnv.env))

       val (elaboratedPairs, metaCtx1) = declPairs.foldLeft((List.empty[Declaration], metaCtx)) {
         case ((acc, currentMetaCtx), (name, (tyTerm, bodyTerm))) =>
            try {
              val (elaboratedTy, metaCtx2) = check(Val.VU, tyTerm, tempTypeEnv, currentMetaCtx)
              val zonkedTy = MetaContext.zonkTerm(metaCtx2, elaboratedTy)
              val tyVal = Eval.eval(zonkedTy, tempTypeEnv.env)
              val (elaboratedBody, metaCtx3) = check(tyVal, bodyTerm, tempTypeEnv, metaCtx2)
              (acc :+ (name, (elaboratedTy, elaboratedBody)), metaCtx3)
           } catch {
             case e: TypeCheckError   => throw TypeCheckError(s"in declaration [$name]:\n${e.msg}")
             case e: ElaborationError => throw ElaborationError(s"in declaration [$name]:\n${e.msg}")
           }
       }

       val unsolved = metaCtx1.unsolvedMetas
       if (unsolved.nonEmpty) {
         throw ElaborationError(
           s"Unsolved metavariables after elaborating declarations at $loc: " +
           unsolved.map(id => s"?$id").mkString(", ")
         )
       }

       val zonkedPairs = elaboratedPairs.map { case (name, (tyTerm, bodyTerm)) =>
         val zt = MetaContext.zonkTerm(metaCtx1, tyTerm)
         val zb = MetaContext.zonkTerm(metaCtx1, bodyTerm)
         (name, (zt, zb))
       }

        val zonkedDecls = Declarations.MutualDecls(loc, zonkedPairs)
        TypeChecker.runDecls(typeEnv, zonkedDecls) match {
          case Right(updatedTypeEnv) => (updatedTypeEnv, metaCtx1, zonkedDecls)
          case Left(err) => throw TypeCheckError(err)
        }

     case Declarations.OpaqueDecl(_) | Declarations.TransparentDecl(_) | Declarations.TransparentAllDecl =>
       TypeChecker.runDecls(typeEnv, decls) match {
         case Right(updatedTypeEnv) => (updatedTypeEnv, metaCtx, decls)
         case Left(err) => throw TypeCheckError(err)
       }
   }

  def elaborateDeclss(typeEnv: TypeEnv, declsList: List[Declarations]): (Option[String], TypeEnv) =
    declsList match {
      case Nil => (None, typeEnv)
      case decl :: rest =>
         try {
           val (updatedTypeEnv, _, _) = elaborateDecls(decl, typeEnv, MetaContext.empty)
           elaborateDeclss(updatedTypeEnv, rest)
        } catch {
          case e: TypeCheckError    => (Some(e.msg), typeEnv)
          case e: ElaborationError  => (Some(e.msg), typeEnv)
        }
    }
}
