package cubical

import scala.collection.immutable.{Map, Set}

// ============================================================
// Names (dimension variables)
// ============================================================

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

// ============================================================
// Directions: 0 or 1
// ============================================================

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
  def fromInt(n: Int): Dir = n match {
    case 0 => Zero
    case 1 => One
    case _ => throw new IllegalArgumentException(s"Dir.fromInt: $n")
  }
}

// ============================================================
// Faces: Map[Name, Dir]
// ============================================================

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

  def compatibles(fs: List[Face]): Boolean = fs match {
    case Nil     => true
    case x :: xs => xs.forall(compatible(x, _)) && compatibles(xs)
  }

  def meet(x: Face, y: Face): Face = {
    if (!compatible(x, y)) throw new RuntimeException(s"meet: incompatible faces")
    x ++ y
  }

  def meetMaybe(x: Face, y: Face): Option[Face] = {
    if (compatible(x, y)) Some(x ++ y) else None
  }

  def meets(xs: List[Face], ys: List[Face]): List[Face] = {
    (for {
      x <- xs
      y <- ys
      if compatible(x, y)
    } yield meet(x, y)).distinct
  }

  def meetss(xss: List[List[Face]]): List[Face] = {
    xss.foldRight(List(eps))(meets)
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

// ============================================================
// Formulas: the de Morgan algebra on interval names
// ============================================================

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

  // Disjunctive normal form
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

  def invFormula(phi: Formula, d: D): List[Face] = (phi, d) match {
    case (Dir(b), _)        => if (b == d) List(Face.eps) else Nil
    case (Atom(i), _)       => List(Face.dir(i, d))
    case (NegAtom(i), _)    => List(Face.dir(i, d.flip))
    case (And(p, q), D.Zero) => (invFormula(p, D.Zero) ++ invFormula(q, D.Zero)).distinct
    case (And(p, q), D.One)  => Face.meets(invFormula(p, D.One), invFormula(q, D.One))
    case (Or(p, q), _)      => invFormula(And(negFormula(p), negFormula(q)), d.flip)
  }
}

// ============================================================
// Nominal typeclass
// ============================================================

trait Nominal[A] {
  def support(a: A): List[Name]
  def act(a: A, sub: (Name, Formula)): A
  def swap(a: A, names: (Name, Name)): A
}

object Nominal {
  def apply[A](using n: Nominal[A]): Nominal[A] = n

  def support[A: Nominal](a: A): List[Name] = Nominal[A].support(a)
  def act[A: Nominal](a: A, sub: (Name, Formula)): A = Nominal[A].act(a, sub)
  def swap[A: Nominal](a: A, names: (Name, Name)): A = Nominal[A].swap(a, names)

  // Fresh name generation
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

  def fresh[A: Nominal](a: A): Name = gensym(support(a))

  def freshs[A: Nominal](a: A): LazyList[Name] = gensyms(support(a))

  // Apply a face substitution: fold over face entries applying Dir substitutions
  def face[A: Nominal](a: A, alpha: Face): A = {
    alpha.foldLeft(a) { case (acc, (i, d)) =>
      act(acc, (i, Formula.Dir(d)))
    }
  }

  // Carve a value using the shape of a system
  def border[A: Nominal](v: A, sys: System[?]): System[A] = {
    sys.map { case (f, _) => f -> face(v, f) }
  }

  // Symmetry: a{i ↦ -i}
  def sym[A: Nominal](a: A, i: Name): A = {
    act(a, (i, Formula.NegAtom(i)))
  }

  // Rename: a{i ↦ j}
  def rename[A: Nominal](a: A, ij: (Name, Name)): A = {
    val (i, j) = ij
    act(a, (i, Formula.Atom(j)))
  }

  // Conjunction: a{i ↦ i ∧ j}
  def conj[A: Nominal](a: A, ij: (Name, Name)): A = {
    val (i, j) = ij
    act(a, (i, Formula.And(Formula.Atom(i), Formula.Atom(j))))
  }

  // Disjunction: a{i ↦ i ∨ j}
  def disj[A: Nominal](a: A, ij: (Name, Name)): A = {
    val (i, j) = ij
    act(a, (i, Formula.Or(Formula.Atom(i), Formula.Atom(j))))
  }

  // ── Helper ──
  def unions[A](xss: List[List[A]]): List[A] = {
    xss.foldRight(List.empty[A]) { (xs, acc) => (xs ++ acc).distinct }
  }

  def unionsMap[A, B](f: A => List[B], xs: List[A]): List[B] = {
    unions(xs.map(f))
  }

  // ── Instances ──────────────────────────────────────────────

  given Nominal[Unit] with {
    def support(a: Unit): List[Name] = Nil
    def act(a: Unit, sub: (Name, Formula)): Unit = ()
    def swap(a: Unit, names: (Name, Name)): Unit = ()
  }

  given Nominal[Name] with {
    def support(a: Name): List[Name] = List(a)
    def act(a: Name, sub: (Name, Formula)): Name = a
    def swap(a: Name, names: (Name, Name)): Name = {
      val (i, j) = names
      Name.swapName(a, i, j)
    }
  }

  given Nominal[Formula] with {
    def support(a: Formula): List[Name] = a match {
      case Formula.Dir(_)        => Nil
      case Formula.Atom(i)       => List(i)
      case Formula.NegAtom(i)    => List(i)
      case Formula.And(phi, psi) => (support(phi) ++ support(psi)).distinct
      case Formula.Or(phi, psi)  => (support(phi) ++ support(psi)).distinct
    }

    def act(a: Formula, sub: (Name, Formula)): Formula = {
      val (i, phi) = sub
      a match {
        case Formula.Dir(b)     => Formula.Dir(b)
        case Formula.Atom(j)    => if (i == j) phi else Formula.Atom(j)
        case Formula.NegAtom(j) => if (i == j) Formula.negFormula(phi) else Formula.NegAtom(j)
        case Formula.And(p, q)  => Formula.andFormula(act(p, sub), act(q, sub))
        case Formula.Or(p, q)   => Formula.orFormula(act(p, sub), act(q, sub))
      }
    }

    def swap(a: Formula, names: (Name, Name)): Formula = {
      val (i, j) = names
      a match {
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
    def support(a: List[A]): List[Name] = unions(a.map(na.support))
    def act(a: List[A], sub: (Name, Formula)): List[A] = a.map(na.act(_, sub))
    def swap(a: List[A], names: (Name, Name)): List[A] = a.map(na.swap(_, names))
  }

  given nominalOption[A](using na: Nominal[A]): Nominal[Option[A]] with {
    def support(a: Option[A]): List[Name] = a.map(na.support).getOrElse(Nil)
    def act(a: Option[A], sub: (Name, Formula)): Option[A] = a.map(na.act(_, sub))
    def swap(a: Option[A], names: (Name, Name)): Option[A] = a.map(na.swap(_, names))
  }

  given nominalPair[A, B](using na: Nominal[A], nb: Nominal[B]): Nominal[(A, B)] with {
    def support(a: (A, B)): List[Name] = (na.support(a._1) ++ nb.support(a._2)).distinct
    def act(a: (A, B), sub: (Name, Formula)): (A, B) = (na.act(a._1, sub), nb.act(a._2, sub))
    def swap(a: (A, B), names: (Name, Name)): (A, B) = (na.swap(a._1, names), nb.swap(a._2, names))
  }

  given nominalTriple[A, B, C](using na: Nominal[A], nb: Nominal[B], nc: Nominal[C]): Nominal[(A, B, C)] with {
    def support(a: (A, B, C)): List[Name] = {
      unions(List(na.support(a._1), nb.support(a._2), nc.support(a._3)))
    }
    def act(a: (A, B, C), sub: (Name, Formula)): (A, B, C) = {
      (na.act(a._1, sub), nb.act(a._2, sub), nc.act(a._3, sub))
    }
    def swap(a: (A, B, C), names: (Name, Name)): (A, B, C) = {
      (na.swap(a._1, names), nb.swap(a._2, names), nc.swap(a._3, names))
    }
  }

  given nominalTuple4[A, B, C, D](using
    na: Nominal[A], nb: Nominal[B], nc: Nominal[C], nd: Nominal[D]
  ): Nominal[(A, B, C, D)] with {
    def support(a: (A, B, C, D)): List[Name] = {
      unions(List(na.support(a._1), nb.support(a._2), nc.support(a._3), nd.support(a._4)))
    }
    def act(a: (A, B, C, D), sub: (Name, Formula)): (A, B, C, D) = {
      (na.act(a._1, sub), nb.act(a._2, sub), nc.act(a._3, sub), nd.act(a._4, sub))
    }
    def swap(a: (A, B, C, D), names: (Name, Name)): (A, B, C, D) = {
      (na.swap(a._1, names), nb.swap(a._2, names), nc.swap(a._3, names), nd.swap(a._4, names))
    }
  }

  given nominalTuple5[A, B, C, D, E](using
    na: Nominal[A], nb: Nominal[B], nc: Nominal[C], nd: Nominal[D], ne: Nominal[E]
  ): Nominal[(A, B, C, D, E)] with {
    def support(a: (A, B, C, D, E)): List[Name] = {
      unions(List(na.support(a._1), nb.support(a._2), nc.support(a._3), nd.support(a._4), ne.support(a._5)))
    }
    def act(a: (A, B, C, D, E), sub: (Name, Formula)): (A, B, C, D, E) = {
      (na.act(a._1, sub), nb.act(a._2, sub), nc.act(a._3, sub), nd.act(a._4, sub), ne.act(a._5, sub))
    }
    def swap(a: (A, B, C, D, E), names: (Name, Name)): (A, B, C, D, E) = {
      (na.swap(a._1, names), nb.swap(a._2, names), nc.swap(a._3, names), nd.swap(a._4, names), ne.swap(a._5, names))
    }
  }

  given nominalTuple6[A, B, C, D, E, H](using
    na: Nominal[A], nb: Nominal[B], nc: Nominal[C], nd: Nominal[D], ne: Nominal[E], nh: Nominal[H]
  ): Nominal[(A, B, C, D, E, H)] with {
    def support(a: (A, B, C, D, E, H)): List[Name] = {
      unions(List(na.support(a._1), nb.support(a._2), nc.support(a._3), nd.support(a._4), ne.support(a._5), nh.support(a._6)))
    }
    def act(a: (A, B, C, D, E, H), sub: (Name, Formula)): (A, B, C, D, E, H) = {
      (na.act(a._1, sub), nb.act(a._2, sub), nc.act(a._3, sub), nd.act(a._4, sub), ne.act(a._5, sub), nh.act(a._6, sub))
    }
    def swap(a: (A, B, C, D, E, H), names: (Name, Name)): (A, B, C, D, E, H) = {
      (na.swap(a._1, names), nb.swap(a._2, names), nc.swap(a._3, names), nd.swap(a._4, names), ne.swap(a._5, names), nh.swap(a._6, names))
    }
  }

  given nominalSystem[A](using na: Nominal[A]): Nominal[System[A]] with {
    def support(s: System[A]): List[Name] = {
      val keyNames: List[Name] = s.keys.toList.flatMap(_.keys)
      val valSupport: List[Name] = unions(s.values.toList.map(na.support))
      (keyNames ++ valSupport).distinct
    }

    def act(s: System[A], sub: (Name, Formula)): System[A] = {
      val (i, phi) = sub
      addAssocs(s.toList, i, phi)
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

// ============================================================
// Nameless wrapper (trivial Nominal instance)
// ============================================================

case class Nameless[A](value: A)

object Nameless {
  given nominalNameless[A]: Nominal[Nameless[A]] with {
    def support(a: Nameless[A]): List[Name] = Nil
    def act(a: Nameless[A], sub: (Name, Formula)): Nameless[A] = a
    def swap(a: Nameless[A], names: (Name, Name)): Nameless[A] = a
  }
}

// ============================================================
// System type and operations
// ============================================================

type System[A] = Map[Face, A]

object SystemOps {
  def empty[A]: System[A] = Map.empty

  def insertSystem[A](alpha: Face, v: A, ts: System[A]): System[A] = {
    if (ts.keys.exists(gamma => Face.leq(alpha, gamma))) {
      ts
    } else {
      val filtered = ts.filter { case (gamma, _) => !Face.leq(gamma, alpha) }
      filtered + (alpha -> v)
    }
  }

  def insertsSystem[A](faces: List[(Face, A)], us: System[A]): System[A] = {
    faces.foldRight(us) { case ((alpha, v), acc) => insertSystem(alpha, v, acc) }
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

  def transposeSystemAndList[A, B](tss: System[List[A]], us: List[B]): List[(System[A], B)] = us match {
    case Nil     => Nil
    case u :: rest =>
      val heads: System[A] = tss.map { case (f, vs) => f -> vs.head }
      val tails: System[List[A]] = tss.map { case (f, vs) => f -> vs.tail }
      (heads, u) :: transposeSystemAndList(tails, rest)
  }

  def leqSystem(alpha: Face, us: System[?]): Boolean = {
    us.keys.exists(beta => Face.leq(alpha, beta))
  }

  def proj[A](us: System[A], alpha: Face)(using na: Nominal[A]): A = {
    val usalpha = Nominal.face[System[A]](us, alpha)
    usalpha.get(Face.eps) match {
      case Some(v) => v
      case None    =>
        throw new RuntimeException(
          s"proj: eps not in $usalpha\nwhich is the $alpha\nface of $us"
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
