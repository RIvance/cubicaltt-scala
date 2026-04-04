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
      val inferredType = TypeChecker.infer(term, typeEnv)
      (term, inferredType, metaCtx)
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
            val (elaboratedArg, metaCtx2) = check(solvedDomain, argTerm, typeEnv, metaCtx1)
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
      case _ => term match {
        case Term.App(_, _, _) if needsElaboration(term, typeEnv) =>
          checkApp(forced, term, typeEnv, metaCtx)
        case _ =>
          // When the expected type is an unsolved meta, try inferring the
          // term's type and solve the meta by unification.
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
              TypeChecker.check(forced, term, typeEnv)
              (term, metaCtx)
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

  /**
   * Elaborate a block of mutual declarations.
   *
   * This is the top-level entry point: for each declaration `x : A = t`,
   * the elaborator infers/checks types and bodies, threads `metaCtx`
   * through, zonks the results, and verifies that all metas are solved.
   *
   * After elaboration the declarations are passed to `TypeChecker.runDecls`
   * for the core type check (which handles the full cubical feature set).
   *
   * @param decls   the mutual declaration block to elaborate
   * @param typeEnv the current typing environment
   * @param metaCtx the current metavariable context (typically `MetaContext.empty`
   *                at the start of each top-level declaration block)
   * @return (updated TypeEnv with the new declarations, updated MetaContext)
   */
  def elaborateDecls(decls: Declarations, typeEnv: TypeEnv, metaCtx: MetaContext): (TypeEnv, MetaContext) = decls match {
    case Declarations.MutualDecls(loc, declPairs) =>
      // Phase 1: Add the declaration block to the environment so that recursive
      // references resolve during elaboration.  We use Environment.addDecl (a Define
      // node) instead of individual addType bindings — this matches how the core
      // TypeChecker builds its checking environment in checkDecls.
      val tempTypeEnv = typeEnv.copy(env = Environment.addDecl(decls, typeEnv.env))

      // Phase 2: Elaborate each declaration, threading metaCtx.
      // For each decl, check the type annotation against U and the body
      // against the elaborated type.  The elaborator inserts implicit lambdas
      // and fresh metas as needed; for non-implicit types it falls through to
      // the core TypeChecker.
      val (elaboratedPairs, metaCtx1) = declPairs.foldLeft((List.empty[Declaration], metaCtx)) {
        case ((acc, currentMetaCtx), (name, (tyTerm, bodyTerm))) =>
          val (elaboratedTy, metaCtx2) = check(Val.VU, tyTerm, tempTypeEnv, currentMetaCtx)
          val tyVal = Eval.eval(elaboratedTy, tempTypeEnv.env)
          val (elaboratedBody, metaCtx3) = check(tyVal, bodyTerm, tempTypeEnv, metaCtx2)
          (acc :+ (name, (elaboratedTy, elaboratedBody)), metaCtx3)
      }

      // Phase 3: Verify all metas are solved
      val unsolved = metaCtx1.unsolvedMetas
      if (unsolved.nonEmpty) {
        throw ElaborationError(
          s"Unsolved metavariables after elaborating declarations at $loc: " +
          unsolved.map(id => s"?$id").mkString(", ")
        )
      }

      // Phase 4: Zonk all elaborated terms (substitute solved metas)
      val zonkedPairs = elaboratedPairs.map { case (name, (tyTerm, bodyTerm)) =>
        val zt = MetaContext.zonkTerm(metaCtx1, tyTerm)
        val zb = MetaContext.zonkTerm(metaCtx1, bodyTerm)
        (name, (zt, zb))
      }

      // Phase 5: Delegate to core TypeChecker for full cubical checking
      val zonkedDecls = Declarations.MutualDecls(loc, zonkedPairs)
      TypeChecker.runDecls(typeEnv, zonkedDecls) match {
        case Right(updatedTypeEnv) => (updatedTypeEnv, metaCtx1)
        case Left(err) => throw TypeCheckError(err)
      }

    // Pragmas pass through unchanged — no metas involved
    case Declarations.OpaqueDecl(_) | Declarations.TransparentDecl(_) | Declarations.TransparentAllDecl =>
      TypeChecker.runDecls(typeEnv, decls) match {
        case Right(updatedTypeEnv) => (updatedTypeEnv, metaCtx)
        case Left(err) => throw TypeCheckError(err)
      }
  }

  /**
   * Elaborate a sequence of declaration blocks.
   *
   * Each block gets a **fresh** `MetaContext` — metas do not leak across
   * top-level declaration groups.  This matches the standard Agda/Lean
   * convention where each top-level definition is elaborated independently.
   *
   * @param typeEnv   the initial typing environment
   * @param declsList the list of declaration blocks to elaborate
   * @return (optional error message, final TypeEnv)
   */
  def elaborateDeclss(typeEnv: TypeEnv, declsList: List[Declarations]): (Option[String], TypeEnv) =
    declsList match {
      case Nil => (None, typeEnv)
      case decl :: rest =>
        try {
          val (updatedTypeEnv, _) = elaborateDecls(decl, typeEnv, MetaContext.empty)
          elaborateDeclss(updatedTypeEnv, rest)
        } catch {
          case e: TypeCheckError    => (Some(e.msg), typeEnv)
          case e: ElaborationError  => (Some(e.msg), typeEnv)
        }
    }
}
