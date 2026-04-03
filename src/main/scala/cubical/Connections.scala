package cubical

import scala.collection.immutable.{Map, Set}

/**
 * A dimension variable: an element of the interval `𝕀`.
 *
 * Names are the "nominal" identifiers used to abstract over interval points.
 * A fresh `Name` is generated whenever a binder `λ̂ i. _` is evaluated; names
 * never collide with term-level `Ident`s because they live in a separate namespace
 * (prefixed with `!` by `Nominal.gensym`).
 */
case class Name(value: String) {
  override def toString: String = value
}

object Name {
  given Ordering[Name] = Ordering.by(_.value)

  def swapName(k: Name, i: Name, j: Name): Name = {
    if (k == i) j
    else if (k == j) i
    else k
  }
}

/**
 * The two endpoints of the interval `𝕀`: `0` and `1`.
 *
 * `Dir` appears as the codomain of a `Face` (a partial map `Name → Dir`) and as
 * concrete formula values `Formula.Dir(Zero)` / `Formula.Dir(One)`.
 *
 * The arithmetic operations match the de Morgan algebra:
 *   - `flip` — negation: `¬0 = 1`, `¬1 = 0`
 *   - `+`    — disjunction: `d₁ ∨ d₂`
 *   - `*`    — conjunction: `d₁ ∧ d₂`
 */
enum Dir {
  case Zero, One

  def flip: Dir = this match {
    case Zero => One
    case One  => Zero
  }

  def +(other: Dir): Dir = (this, other) match {
    case (Zero, Zero) => Zero
    case _            => One
  }

  def *(other: Dir): Dir = (this, other) match {
    case (Zero, _) => Zero
    case (One, x)  => x
  }

  override def toString: String = this match {
    case Zero => "0"
    case One  => "1"
  }
}

object Dir {
  def fromInt(intValue: Int): Dir = intValue match {
    case 0 => Zero
    case 1 => One
    case _ => throw new IllegalArgumentException(s"Dir.fromInt: $intValue")
  }
}

/**
 * A face: a finite partial map `Name → Dir`, written `(i₁=d₁, …, iₙ=dₙ)`.
 *
 * Faces form a bounded lattice under `leq` (reverse refinement order):
 *   - `eps` (the empty map) is the top element — the "everywhere" face.
 *   - `meet α β` is the union `α ∪ β` when `α` and `β` are compatible (agree on
 *     shared names), making them more specific.
 *
 * A face `α` restricts a type or value to the sub-cube where each `iₖ = dₖ`.
 * The `act` operation on a `Nominal[A]` value applies `α` as a simultaneous
 * dimension substitution.
 */
type Face = Map[Name, Dir]

object Face {
  val eps: Face = Map.empty

  def dir(i: Name, d: Dir): Face = Map(i -> d)

  def showFace(alpha: Face): String = {
    alpha.toList.sortBy(_._1).map { case (i, d) => s"($i = $d)" }.mkString
  }

  def swapFace(alpha: Face, ij: (Name, Name)): Face = {
    val (i, j) = ij
    alpha.map { case (k, d) => Name.swapName(k, i, j) -> d }
  }

  def compatible(xs: Face, ys: Face): Boolean = {
    xs.forall { case (k, d) =>
      ys.get(k).forall(_ == d)
    }
  }

  def compatibles(faces: List[Face]): Boolean = faces match {
    case Nil     => true
    case x :: xs => xs.forall(compatible(x, _)) && compatibles(xs)
  }

  def meet(left: Face, right: Face): Face = {
    if (!compatible(left, right)) throw new RuntimeException(s"meet: incompatible faces")
    left ++ right
  }

  def meetMaybe(left: Face, right: Face): Option[Face] = {
    if (compatible(left, right)) Some(left ++ right) else None
  }

  def meets(xs: List[Face], ys: List[Face]): List[Face] = {
    (for {
      x <- xs
      y <- ys
      if compatible(x, y)
    } yield meet(x, y)).distinct
  }

  def meetss(faceLists: List[List[Face]]): List[Face] = {
    faceLists.foldRight(List(eps))(meets)
  }

  def leq(alpha: Face, beta: Face): Boolean = {
    meetMaybe(alpha, beta) == Some(alpha)
  }

  def comparable(alpha: Face, beta: Face): Boolean = {
    leq(alpha, beta) || leq(beta, alpha)
  }

  def incomparables(fs: List[Face]): Boolean = fs match {
    case Nil     => true
    case x :: xs => xs.forall(y => !comparable(x, y)) && incomparables(xs)
  }

  def minus(alpha: Face, beta: Face): Face = {
    alpha.removedAll(beta.keys)
  }
}

/**
 * A formula `φ` over dimension variables: an element of the free de Morgan
 * algebra on `Name`.
 *
 * The interval `𝕀` has two endpoints `0` and `1`, so formulas describe
 * sub-cubes of the ambient dimension context.  A formula `φ` evaluates to
 * `1` on exactly those faces where `φ` holds, giving the "extent" of a
 * partial element `[φ ↦ u]`.
 *
 * Connectives:
 *   - `Dir(d)` — constant `0` or `1`
 *   - `Atom(i)` — dimension variable `i`, identifying the face `(i = 1)`
 *   - `NegAtom(i)` — negation `¬i`, the face `(i = 0)`
 *   - `And(φ, ψ)` — `φ ∧ ψ`  (conjunction / meet of faces)
 *   - `Or(φ, ψ)`  — `φ ∨ ψ`  (disjunction / join of faces)
 *
 * Satisfying de Morgan duality: `¬(φ ∧ ψ) = ¬φ ∨ ¬ψ` and `¬(φ ∨ ψ) = ¬φ ∧ ¬ψ`.
 */
enum Formula {
  case Dir(d: cubical.Dir)
  case Atom(name: Name)
  case NegAtom(name: Name)
  case And(phi: Formula, psi: Formula)
  case Or(phi: Formula, psi: Formula)

  override def toString: String = this match {
    case Formula.Dir(d)       => d.toString
    case Formula.Atom(n)      => n.toString
    case Formula.NegAtom(n)   => s"-$n"
    case Formula.Or(a, b)     =>
      def show1(v: Formula): String = v match {
        case Formula.And(_, _) => s"($v)"
        case _                 => v.toString
      }
      s"${show1(a)} \\/ ${show1(b)}"
    case Formula.And(a, b)    =>
      def show1(v: Formula): String = v match {
        case Formula.Or(_, _) => s"($v)"
        case _                => v.toString
      }
      s"${show1(a)} /\\ ${show1(b)}"
  }
}

object Formula {
  import cubical.{Dir => D}

  def negFormula(phi: Formula): Formula = phi match {
    case Dir(d)        => Dir(d.flip)
    case Atom(i)       => NegAtom(i)
    case NegAtom(i)    => Atom(i)
    case And(phi, psi) => orFormula(negFormula(phi), negFormula(psi))
    case Or(phi, psi)  => andFormula(negFormula(phi), negFormula(psi))
  }

  def andFormula(phi: Formula, psi: Formula): Formula = (phi, psi) match {
    case (Dir(D.Zero), _) => Dir(D.Zero)
    case (_, Dir(D.Zero)) => Dir(D.Zero)
    case (Dir(D.One), p)  => p
    case (p, Dir(D.One))  => p
    case (p, q)           => And(p, q)
  }

  def orFormula(phi: Formula, psi: Formula): Formula = (phi, psi) match {
    case (Dir(D.One), _)  => Dir(D.One)
    case (_, Dir(D.One))  => Dir(D.One)
    case (Dir(D.Zero), p) => p
    case (p, Dir(D.Zero)) => p
    case (p, q)           => Or(p, q)
  }

  /**
   * Reduce `φ` to disjunctive normal form (a set of conjunctive clauses).
   *
   * Each inner `Set[(Name, D)]` is a conjunction of literals; the outer `Set` is
   * their disjunction.  The empty inner set represents `1` (tautology); the empty
   * outer set represents `0` (contradiction).  Redundant clauses (supersets of
   * smaller clauses) are removed by `merge`.
   */
  def dnf(phi: Formula): Set[Set[(Name, D)]] = phi match {
    case Dir(D.One)    => Set(Set.empty)
    case Dir(D.Zero)   => Set.empty
    case Atom(n)       => Set(Set((n, D.One)))
    case NegAtom(n)    => Set(Set((n, D.Zero)))
    case Or(p, q)      => merge(dnf(p), dnf(q))
    case And(p, q)     =>
      val dp = dnf(p).toList
      val dq = dnf(q).toList
      val combined = for { a <- dp; b <- dq } yield a.union(b)
      combined.foldLeft(Set.empty[Set[(Name, D)]])((acc, s) => merge(acc, Set(s)))
  }

  def fromDNF(s: Set[Set[(Name, D)]]): Formula = {
    val xss = s.toList.map(_.toList)
    val fs = xss.map { xs =>
      xs.map { case (n, d) => if (d == D.Zero) NegAtom(n) else Atom(n) }
    }
    fs.foldRight(Dir(D.Zero): Formula) { (clause, acc) =>
      orFormula(clause.foldRight(Dir(D.One): Formula)(andFormula), acc)
    }
  }

  def merge(
    a: Set[Set[(Name, D)]],
    b: Set[Set[(Name, D)]]
  ): Set[Set[(Name, D)]] = {
    val as = a.toList
    val bs = b.toList
    val filteredA = as.filter(ai => !bs.exists(bi => bi.subsetOf(ai) && bi != ai))
    val filteredB = bs.filter(bi => !as.exists(ai => ai.subsetOf(bi) && ai != bi))
    filteredA.toSet.union(filteredB.toSet)
  }

  /**
   * Compute the pre-image of direction `d` under formula `φ`.
   *
   * Returns a list of faces `α` such that `φ[α] = d`.  Used in `evalSystem` to
   * propagate dimension substitutions into partial systems.
   */
  def invFormula(phi: Formula, d: D): List[Face] = (phi, d) match {
    case (Dir(b), _)        => if (b == d) List(Face.eps) else Nil
    case (Atom(i), _)       => List(Face.dir(i, d))
    case (NegAtom(i), _)    => List(Face.dir(i, d.flip))
    case (And(p, q), D.Zero) => (invFormula(p, D.Zero) ++ invFormula(q, D.Zero)).distinct
    case (And(p, q), D.One)  => Face.meets(invFormula(p, D.One), invFormula(q, D.One))
    case (Or(p, q), _)      => invFormula(And(negFormula(p), negFormula(q)), d.flip)
  }
}

/**
 * The `Nominal` typeclass: types that carry a free action of the group of
 * dimension-variable permutations and support dimension substitution.
 *
 * Three operations:
 *   - `support(a)` — the finite set of `Name`s that `a` depends on.
 *     The action of any permutation fixing `support(a)` fixes `a`.
 *   - `act(a, (i, φ))` — dimension substitution `a[i ↦ φ]`.
 *     Replaces every free occurrence of dimension variable `i` in `a` with `φ`.
 *   - `swap(a, (i, j))` — name transposition `a(i j)`.
 *     Swaps all occurrences of `i` and `j` without substituting formulas.
 *
 * Instances are provided for all semantic objects: `Val`, `Environment`,
 * `Formula`, `System[A]`, and their products/lists.
 */
trait Nominal[A] {
  def support(value: A): List[Name]
  def act(value: A, sub: (Name, Formula)): A
  def swap(value: A, names: (Name, Name)): A
}

object Nominal {
  def apply[A](using n: Nominal[A]): Nominal[A] = n

  def support[A: Nominal](value: A): List[Name] = Nominal[A].support(value)
  def act[A: Nominal](value: A, sub: (Name, Formula)): A = Nominal[A].act(value, sub)
  def swap[A: Nominal](value: A, names: (Name, Name)): A = Nominal[A].swap(value, names)

  /**
   * Generate the least fresh `Name` not already in `xs`.
   *
   * Names are of the form `!n` for non-negative integers `n`, chosen to be
   * syntactically distinct from user-level names in `.ctt` source.
   */
  def gensym(xs: List[Name]): Name = {
    val nums = xs.collect {
      case Name(s) if s.startsWith("!") =>
        scala.util.Try(s.drop(1).toInt).getOrElse(0)
    }
    val max = if (nums.isEmpty) 0 else nums.max + 1
    Name("!" + max)
  }

  def gensyms(d: List[Name]): LazyList[Name] = {
    val x = gensym(d)
    x #:: gensyms(x :: d)
  }

  def fresh[A: Nominal](value: A): Name = gensym(support(value))

  def freshs[A: Nominal](value: A): LazyList[Name] = gensyms(support(value))

  /** Apply a face `α` as a simultaneous substitution `[i₁ ↦ d₁, …, iₙ ↦ dₙ]`. */
  def face[A: Nominal](value: A, alpha: Face): A = {
    alpha.foldLeft(value) { case (acc, (i, d)) =>
      act(acc, (i, Formula.Dir(d)))
    }
  }

  /** Restrict `value` to each face in `sys`, returning a system of the same shape. */
  def border[A: Nominal](value: A, sys: System[?]): System[A] = {
    sys.map { case (f, _) => f -> face(value, f) }
  }

  /** Symmetry `a{i ↦ ¬i}` — reverses the direction of dimension `i`. */
  def sym[A: Nominal](value: A, i: Name): A = {
    act(value, (i, Formula.NegAtom(i)))
  }

  /** Rename `a{i ↦ j}` — substitute dimension `i` with `j`. */
  def rename[A: Nominal](value: A, ij: (Name, Name)): A = {
    val (i, j) = ij
    act(value, (i, Formula.Atom(j)))
  }

  /** Conjunction `a{i ↦ i ∧ j}` — used in the filling construction. */
  def conj[A: Nominal](value: A, ij: (Name, Name)): A = {
    val (i, j) = ij
    act(value, (i, Formula.And(Formula.Atom(i), Formula.Atom(j))))
  }

  /** Disjunction `a{i ↦ i ∨ j}` — used in the squeeze construction. */
  def disj[A: Nominal](value: A, ij: (Name, Name)): A = {
    val (i, j) = ij
    act(value, (i, Formula.Or(Formula.Atom(i), Formula.Atom(j))))
  }

  def unions[A](lists: List[List[A]]): List[A] = {
    lists.foldRight(List.empty[A]) { (xs, acc) => (xs ++ acc).distinct }
  }

  def unionsMap[A, B](fn: A => List[B], items: List[A]): List[B] = {
    unions(items.map(fn))
  }

  /**
   * `Nominal` instances for primitive and compound types.
   *
   * Products, lists, options, and tuples up to arity 6 are derived
   * componentwise.  `System[A]` is the most complex instance: `act` must
   * re-index each face key through `invFormula` when the substituted name
   * appears in the key, expanding a single face into potentially many faces
   * in the refined system.
   */

  given Nominal[Unit] with {
    def support(unit: Unit): List[Name] = Nil
    def act(unit: Unit, sub: (Name, Formula)): Unit = ()
    def swap(unit: Unit, names: (Name, Name)): Unit = ()
  }

  given Nominal[Name] with {
    def support(name: Name): List[Name] = List(name)
    def act(name: Name, sub: (Name, Formula)): Name = name
    def swap(name: Name, names: (Name, Name)): Name = {
      val (i, j) = names
      Name.swapName(name, i, j)
    }
  }

  given Nominal[Formula] with {
    def support(formula: Formula): List[Name] = formula match {
      case Formula.Dir(_)        => Nil
      case Formula.Atom(i)       => List(i)
      case Formula.NegAtom(i)    => List(i)
      case Formula.And(phi, psi) => (support(phi) ++ support(psi)).distinct
      case Formula.Or(phi, psi)  => (support(phi) ++ support(psi)).distinct
    }

    def act(formula: Formula, sub: (Name, Formula)): Formula = {
      val (i, phi) = sub
      formula match {
        case Formula.Dir(b)     => Formula.Dir(b)
        case Formula.Atom(j)    => if (i == j) phi else Formula.Atom(j)
        case Formula.NegAtom(j) => if (i == j) Formula.negFormula(phi) else Formula.NegAtom(j)
        case Formula.And(p, q)  => Formula.andFormula(act(p, sub), act(q, sub))
        case Formula.Or(p, q)   => Formula.orFormula(act(p, sub), act(q, sub))
      }
    }

    def swap(formula: Formula, names: (Name, Name)): Formula = {
      val (i, j) = names
      formula match {
        case Formula.Dir(b)     => Formula.Dir(b)
        case Formula.Atom(k)    =>
          if (k == i) Formula.Atom(j)
          else if (k == j) Formula.Atom(i)
          else Formula.Atom(k)
        case Formula.NegAtom(k) =>
          if (k == i) Formula.NegAtom(j)
          else if (k == j) Formula.NegAtom(i)
          else Formula.NegAtom(k)
        case Formula.And(p, q)  => Formula.And(swap(p, names), swap(q, names))
        case Formula.Or(p, q)   => Formula.Or(swap(p, names), swap(q, names))
      }
    }
  }

  given nominalList[A](using na: Nominal[A]): Nominal[List[A]] with {
    def support(list: List[A]): List[Name] = unions(list.map(na.support))
    def act(list: List[A], sub: (Name, Formula)): List[A] = list.map(na.act(_, sub))
    def swap(list: List[A], names: (Name, Name)): List[A] = list.map(na.swap(_, names))
  }

  given nominalOption[A](using na: Nominal[A]): Nominal[Option[A]] with {
    def support(opt: Option[A]): List[Name] = opt.map(na.support).getOrElse(Nil)
    def act(opt: Option[A], sub: (Name, Formula)): Option[A] = opt.map(na.act(_, sub))
    def swap(opt: Option[A], names: (Name, Name)): Option[A] = opt.map(na.swap(_, names))
  }

  given nominalPair[A, B](using na: Nominal[A], nb: Nominal[B]): Nominal[(A, B)] with {
    def support(pair: (A, B)): List[Name] = (na.support(pair._1) ++ nb.support(pair._2)).distinct
    def act(pair: (A, B), sub: (Name, Formula)): (A, B) = (na.act(pair._1, sub), nb.act(pair._2, sub))
    def swap(pair: (A, B), names: (Name, Name)): (A, B) = (na.swap(pair._1, names), nb.swap(pair._2, names))
  }

  given nominalTriple[A, B, C](using na: Nominal[A], nb: Nominal[B], nc: Nominal[C]): Nominal[(A, B, C)] with {
    def support(tuple: (A, B, C)): List[Name] = {
      unions(List(na.support(tuple._1), nb.support(tuple._2), nc.support(tuple._3)))
    }
    def act(tuple: (A, B, C), sub: (Name, Formula)): (A, B, C) = {
      (na.act(tuple._1, sub), nb.act(tuple._2, sub), nc.act(tuple._3, sub))
    }
    def swap(tuple: (A, B, C), names: (Name, Name)): (A, B, C) = {
      (na.swap(tuple._1, names), nb.swap(tuple._2, names), nc.swap(tuple._3, names))
    }
  }

  given nominalTuple4[A, B, C, D](using
    na: Nominal[A], nb: Nominal[B], nc: Nominal[C], nd: Nominal[D]
  ): Nominal[(A, B, C, D)] with {
    def support(tuple: (A, B, C, D)): List[Name] = {
      unions(List(na.support(tuple._1), nb.support(tuple._2), nc.support(tuple._3), nd.support(tuple._4)))
    }
    def act(tuple: (A, B, C, D), sub: (Name, Formula)): (A, B, C, D) = {
      (na.act(tuple._1, sub), nb.act(tuple._2, sub), nc.act(tuple._3, sub), nd.act(tuple._4, sub))
    }
    def swap(tuple: (A, B, C, D), names: (Name, Name)): (A, B, C, D) = {
      (na.swap(tuple._1, names), nb.swap(tuple._2, names), nc.swap(tuple._3, names), nd.swap(tuple._4, names))
    }
  }

  given nominalTuple5[A, B, C, D, E](using
    na: Nominal[A], nb: Nominal[B], nc: Nominal[C], nd: Nominal[D], ne: Nominal[E]
  ): Nominal[(A, B, C, D, E)] with {
    def support(tuple: (A, B, C, D, E)): List[Name] = {
      unions(List(na.support(tuple._1), nb.support(tuple._2), nc.support(tuple._3), nd.support(tuple._4), ne.support(tuple._5)))
    }
    def act(tuple: (A, B, C, D, E), sub: (Name, Formula)): (A, B, C, D, E) = {
      (na.act(tuple._1, sub), nb.act(tuple._2, sub), nc.act(tuple._3, sub), nd.act(tuple._4, sub), ne.act(tuple._5, sub))
    }
    def swap(tuple: (A, B, C, D, E), names: (Name, Name)): (A, B, C, D, E) = {
      (na.swap(tuple._1, names), nb.swap(tuple._2, names), nc.swap(tuple._3, names), nd.swap(tuple._4, names), ne.swap(tuple._5, names))
    }
  }

  given nominalTuple6[A, B, C, D, E, H](using
    na: Nominal[A], nb: Nominal[B], nc: Nominal[C], nd: Nominal[D], ne: Nominal[E], nh: Nominal[H]
  ): Nominal[(A, B, C, D, E, H)] with {
    def support(tuple: (A, B, C, D, E, H)): List[Name] = {
      unions(List(na.support(tuple._1), nb.support(tuple._2), nc.support(tuple._3), nd.support(tuple._4), ne.support(tuple._5), nh.support(tuple._6)))
    }
    def act(tuple: (A, B, C, D, E, H), sub: (Name, Formula)): (A, B, C, D, E, H) = {
      (na.act(tuple._1, sub), nb.act(tuple._2, sub), nc.act(tuple._3, sub), nd.act(tuple._4, sub), ne.act(tuple._5, sub), nh.act(tuple._6, sub))
    }
    def swap(tuple: (A, B, C, D, E, H), names: (Name, Name)): (A, B, C, D, E, H) = {
      (na.swap(tuple._1, names), nb.swap(tuple._2, names), nc.swap(tuple._3, names), nd.swap(tuple._4, names), ne.swap(tuple._5, names), nh.swap(tuple._6, names))
    }
  }

  given nominalSystem[A](using na: Nominal[A]): Nominal[System[A]] with {
    def support(sys: System[A]): List[Name] = {
      val keyNames: List[Name] = sys.keys.toList.flatMap(_.keys)
      val valSupport: List[Name] = unions(sys.values.toList.map(na.support))
      (keyNames ++ valSupport).distinct
    }

    def act(sys: System[A], sub: (Name, Formula)): System[A] = {
      val (i, phi) = sub
      addAssocs(sys.toList, i, phi)
    }

    private def addAssocs(assocs: List[(Face, A)], i: Name, phi: Formula): System[A] = assocs match {
      case Nil => Map.empty
      case (alpha, u) :: rest =>
        val s2 = addAssocs(rest, i, phi)
        alpha.get(i) match {
          case Some(d) =>
            val beta = alpha.removed(i)
            val phiFaceBeta = Nominal.face[Formula](phi, beta)
            val deltas = Formula.invFormula(phiFaceBeta, d)
            deltas.foldRight(s2) { (delta, acc) =>
              val meetDeltaBeta = Face.meet(delta, beta)
              val uFace = Nominal.face[A](u, Face.minus(delta, Map(i -> d)))
              SystemOps.insertSystem(meetDeltaBeta, uFace, acc)
            }
          case None =>
            val phiFaceAlpha = Nominal.face[Formula](phi, alpha)
            SystemOps.insertSystem(alpha, na.act(u, (i, phiFaceAlpha)), s2)
        }
    }

    def swap(s: System[A], names: (Name, Name)): System[A] = {
      s.map { case (alpha, v) =>
        Face.swapFace(alpha, names) -> na.swap(v, names)
      }
    }
  }
}

/**
 * A wrapper that gives any type `A` a trivial `Nominal` instance.
 *
 * `Nameless[A]` has empty support and is fixed by all dimension substitutions
 * and swaps.  Used to embed non-nominal data (e.g. the opaque-name set
 * `Set[Ident]`) inside `Environment` without polluting the nominal structure.
 */
case class Nameless[A](value: A)

object Nameless {
  given nominalNameless[A]: Nominal[Nameless[A]] with {
    def support(nameless: Nameless[A]): List[Name] = Nil
    def act(nameless: Nameless[A], sub: (Name, Formula)): Nameless[A] = nameless
    def swap(nameless: Nameless[A], names: (Name, Name)): Nameless[A] = nameless
  }
}

/**
 * A partial element at a system of faces: `[α₁ ↦ u₁, …, αₙ ↦ uₙ]`.
 *
 * `System[A]` is `Map[Face, A]` — each key `αᵢ` is a face and the corresponding
 * value `uᵢ : A` is the component defined on that face.  The map is kept in
 * "reduced" form: no face `αᵢ` is more specific than another (i.e. `¬(αᵢ ≤ αⱼ)`
 * for `i ≠ j`), enforced by `SystemOps.insertSystem`.
 *
 * The empty system `[]` represents the everywhere-undefined partial element
 * (the empty box).  The system `[ε ↦ u]` (key = `eps`) represents a total
 * element `u` defined everywhere.
 */
type System[A] = Map[Face, A]

object SystemOps {
  def empty[A]: System[A] = Map.empty

  /**
   * Insert `(alpha, insertedVal)` into `sys`, maintaining the invariant that no
   * face in the result is a strict refinement of another.
   *
   * If `sys` already contains a face `γ ≤ alpha` (more general), `alpha` is
   * redundant and discarded.  Otherwise all existing faces `γ ≥ alpha` (more
   * specific) are removed before inserting `alpha`.
   */
  def insertSystem[A](alpha: Face, insertedVal: A, sys: System[A]): System[A] = {
    if (sys.keys.exists(gamma => Face.leq(alpha, gamma))) {
      sys
    } else {
      val filtered = sys.filter { case (gamma, _) => !Face.leq(gamma, alpha) }
      filtered + (alpha -> insertedVal)
    }
  }

  def insertsSystem[A](faces: List[(Face, A)], sys: System[A]): System[A] = {
    faces.foldRight(sys) { case ((alpha, v), acc) => insertSystem(alpha, v, acc) }
  }

  def mkSystem[A](pairs: List[(Face, A)]): System[A] = {
    insertsSystem(pairs, Map.empty)
  }

  def unionSystem[A](us: System[A], vs: System[A]): System[A] = {
    insertsSystem(us.toList, vs)
  }

  def joinSystem[A](tss: System[System[A]]): System[A] = {
    mkSystem(
      for {
        (alpha, ts) <- tss.toList
        (beta, t)   <- ts.toList
      } yield (Face.meet(alpha, beta), t)
    )
  }

  def transposeSystemAndList[A, B](sys: System[List[A]], items: List[B]): List[(System[A], B)] = items match {
    case Nil     => Nil
    case item :: rest =>
      val heads: System[A] = sys.map { case (f, vs) => f -> vs.head }
      val tails: System[List[A]] = sys.map { case (f, vs) => f -> vs.tail }
      (heads, item) :: transposeSystemAndList(tails, rest)
  }

  def leqSystem(alpha: Face, sys: System[?]): Boolean = {
    sys.keys.exists(beta => Face.leq(alpha, beta))
  }

  def proj[A](sys: System[A], alpha: Face)(using na: Nominal[A]): A = {
    val sysFaced = Nominal.face[System[A]](sys, alpha)
    sysFaced.get(Face.eps) match {
      case Some(v) => v
      case None    =>
        throw new RuntimeException(
          s"proj: eps not in $sysFaced\nwhich is the $alpha\nface of $sys"
        )
      }
    }

  def domain(sys: System[?]): List[Name] = {
    sys.keys.flatMap(_.keys).toList.distinct
  }

  def showSystem[A](sys: System[A])(using show: A => String): String = {
    if (sys.isEmpty) "[]"
    else {
      val entries = sys.toList.map { case (alpha, u) =>
        s"${Face.showFace(alpha)} -> ${show(u)}"
      }
      s"[ ${entries.mkString(", ")} ]"
    }
  }

  def showSystemVal(sys: System[?]): String = {
    if (sys.isEmpty) "[]"
    else {
      val entries = sys.toList.map { case (alpha, u) =>
        s"${Face.showFace(alpha)} -> $u"
      }
      s"[ ${entries.mkString(", ")} ]"
    }
  }
}
