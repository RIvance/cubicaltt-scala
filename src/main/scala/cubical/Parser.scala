package cubical

import scala.util.parsing.combinator.*
import scala.util.parsing.input.{Reader, Position, NoPosition}

/**
 * Thrown when parsing fails (syntax error, unexpected token, etc.).
 *
 * Mirrors `ResolveError`, `TypeCheckError`, and `EvalError` in the rest of the pipeline.
 */
case class ParseError(msg: String) extends RuntimeException(msg)

/**
 * A `Reader[String]` that wraps a pre-tokenised `IndexedSeq[String]` produced
 * by `LayoutPreprocessor.preprocess`.  Position is reported as a 1-based
 * column offset into the token sequence (not into the source text; source
 * positions were already discarded by the layout preprocessor).
 *
 * This reader is consumed by `CubicalParser`, which extends `Parsers`
 * and requires a `Reader` over the token element type.
 */
private class TokenReader(tokens: IndexedSeq[String], offset: Int) extends Reader[String] {
  def first: String   = if (atEnd) "" else tokens(offset)
  def rest: Reader[String] = new TokenReader(tokens, offset + 1)
  def atEnd: Boolean  = offset >= tokens.length
  def pos: Position   = new Position {
    def line: Int    = 1
    def column: Int  = offset + 1
    def lineContents: String = tokens.drop(offset).take(5).mkString(" ")
  }
}

/**
 * Purely syntactic parser for `.ctt` files.
 *
 * Produces `RawTerm` / `RawDecl` / `RawModule` trees with no name resolution.
 * All identifiers appear as plain `String`s; the distinction between variables,
 * constructors, path constructors, and dimension names is established by
 * `Resolver`.
 *
 * Uses `Parsers` over a `TokenReader` fed from `LayoutPreprocessor`.
 * The grammar is LL-style with no left recursion, so plain `Parsers`
 * suffices and avoids the unbounded O(n × rules) memoisation cache
 * that `PackratParsers` would allocate.
 */
private[cubical] class CubicalParser extends Parsers {

  override type Elem = String

  private var locCounter: Int = 0
  private def freshLoc(): Loc = { locCounter += 1; Loc("", locCounter, 0) }

  private val keywords: Set[String] = Set(
    "module", "where", "let", "in", "split", "with", "mutual",
    "import", "data", "hdata", "undefined", "PathP", "comp",
    "transport", "fill", "Glue", "glue", "unglue", "U",
    "opaque", "transparent", "transparent_all", "Id", "idC", "idJ",
    "split@"
  )

  private def tok(t: String): Parser[String] = elem(t, _ == t)

  private def kw(t: String): Parser[String] = elem(t, _ == t)

  private def identToken: Parser[String] =
    elem("identifier", s => {
      if (keywords.contains(s)) false
      else if (s.matches("[a-zA-Z_][a-zA-Z0-9_']*")) true
      else if (s.matches("![0-9]*")) true
      else false
    })

  def ident: Parser[String] = identToken

  def holeIdent: Parser[String] = tok("?")

  private def run[A](p: Parser[A], source: String): A = {
    locCounter = 0
    val tokens = LayoutPreprocessor.preprocess(source).toIndexedSeq
    val reader = new TokenReader(tokens, 0)
    phrase(p)(reader) match {
      case Success(result, _) => result
      case Failure(msg, next) => throw ParseError(s"Parse error at token ${next.pos.column}: $msg")
      case Error(msg, next)   => throw ParseError(s"Parse error at token ${next.pos.column}: $msg")
    }
  }

  def parseImports(source: String): ParsedImports =
    run(moduleImportsParser <~ rep(elem("any token", _ => true)), source)

  def parseRawModule(source: String): RawModule =
    run(moduleParser, source)

  def parseRawExpression(source: String): RawTerm =
    run(expr, source)

  private def moduleImportsParser: Parser[ParsedImports] =
    kw("module") ~> ident ~ (kw("where") ~> tok("{") ~> rep(imp <~ tok(";"))) ^^ {
      case name ~ imps => ParsedImports(name, imps)
    }

  private def moduleParser: Parser[RawModule] =
    kw("module") ~> ident ~ (kw("where") ~> tok("{") ~> impsAndDeclsBlock <~ tok("}")) ^^ {
      case name ~ ((imports, decls)) => RawModule(name, imports, decls)
    }

  private def impsAndDeclsBlock: Parser[(List[String], List[RawDecl])] =
    repsep(impOrDecl, tok(";")) ^^ { items =>
      val imports = items.collect { case Left(i) => i }
      val decls   = items.collect { case Right(d) => d }
      (imports, decls)
    }

  private def impOrDecl: Parser[Either[String, RawDecl]] =
    imp ^^ { Left(_) } | rawDecl ^^ { Right(_) }

  def imp: Parser[String] = kw("import") ~> ident

  def dir: Parser[Dir] =
    tok("0") ^^^ Dir.Zero | tok("1") ^^^ Dir.One

  /** Negate a raw formula, applying De Morgan's laws for compound formulas. */
  private def negRawFormula(phi: RawFormula): RawFormula = phi match {
    case RawFormula.Dir(d)      => RawFormula.Dir(d.flip)
    case RawFormula.Atom(x)     => RawFormula.NegAtom(x)
    case RawFormula.NegAtom(x)  => RawFormula.Atom(x)
    case RawFormula.And(a, b)   => RawFormula.Or(negRawFormula(a), negRawFormula(b))
    case RawFormula.Or(a, b)    => RawFormula.And(negRawFormula(a), negRawFormula(b))
  }

  def formula: Parser[RawFormula] = formulaDisj

  lazy val formulaDisj: Parser[RawFormula] =
    formulaConj ~ rep(tok("\\/") ~> formulaConj) ^^ {
      case f ~ fs => fs.foldLeft(f)((acc, g) => RawFormula.Or(acc, g))
    }

  lazy val formulaConj: Parser[RawFormula] =
    formulaAtom ~ rep(tok("/\\") ~> formulaAtom) ^^ {
      case f ~ fs => fs.foldLeft(f)((acc, g) => RawFormula.And(acc, g))
    }

  lazy val formulaAtom: Parser[RawFormula] =
    tok("-") ~> formulaAtom ^^ { negRawFormula } |
    dir ^^ { (d: cubical.Dir) => RawFormula.Dir(d) } |
    ident ^^ { name => RawFormula.Atom(name) } |
    tok("(") ~> formula <~ tok(")")

  def face: Parser[(String, Dir)] =
    tok("(") ~> ident ~ (tok("=") ~> dir) <~ tok(")") ^^ { case name ~ d => (name, d) }

  def faceMap: Parser[RawFace] =
    rep(face) ^^ { pairs => pairs.toMap }

  def side: Parser[(RawFace, RawTerm)] =
    faceMap ~ (tok("->") ~> expr) ^^ { case alpha ~ e => (alpha, e) }

  def system: Parser[RawSystem] =
    tok("[") ~> repsep(side, tok(",")) <~ tok("]") ^^ { _.toMap }

  def teleEntry: Parser[List[(String, RawTerm)]] =
    tok("(") ~> rep1(ident) ~ (tok(":") ~> expr) <~ tok(")") ^^ {
      case names ~ ty => names.map(n => (n, ty))
    }

  def telescope: Parser[List[(String, RawTerm)]] =
    rep(teleEntry) ^^ { _.flatten }

  /**
   * A single telescope entry, either explicit `(x₁ x₂ : A)` or implicit `{x₁ x₂ : A}`.
   * Returns a list of `(Icity, name, type)` triples.
   */
  def icityTeleEntry: Parser[List[(Icity, String, RawTerm)]] =
    tok("(") ~> rep1(ident) ~ (tok(":") ~> expr) <~ tok(")") ^^ {
      case names ~ ty => names.map(n => (Icity.Explicit, n, ty))
    } |
    tok("{") ~> rep1(ident) ~ (tok(":") ~> expr) <~ tok("}") ^^ {
      case names ~ ty => names.map(n => (Icity.Implicit, n, ty))
    }

  /**
   * A telescope with icity annotations: `(x : A) {y : B} (z : C)`.
   * Requires at least one entry.
   */
  def icityTele: Parser[List[(Icity, String, RawTerm)]] =
    rep1(icityTeleEntry) ^^ { _.flatten }

  def pathTeleEntry: Parser[List[(String, RawTerm)]] =
    tok("(") ~> rep1(ident) ~ (tok(":") ~> expr) <~ tok(")") ^^ {
      case names ~ ty => names.map(n => (n, ty))
    }

  def pathTele: Parser[List[(String, RawTerm)]] =
    rep1(pathTeleEntry) ^^ { _.flatten }

  lazy val expr: Parser[RawTerm] = expr0

  lazy val expr0: Parser[RawTerm] =
    letExpr | lamExpr | plamExpr | splitAtExpr | expr1

  lazy val letExpr: Parser[RawTerm] =
    kw("let") ~> tok("{") ~> rawDeclsBlock ~ (tok("}") ~> kw("in") ~> expr) ^^ {
      case rawDecls ~ body => RawTerm.Where(body, rawDecls)
    }

  lazy val lamExpr: Parser[RawTerm] =
    tok("\\") ~> icityTele ~ (tok("->") ~> expr) ^^ {
      case tele ~ body => buildIcityLams(tele, body)
    }

  lazy val plamExpr: Parser[RawTerm] =
    tok("<") ~> rep1(ident) ~ (tok(">") ~> expr) ^^ {
      case names ~ body => names.foldRight(body) { (name, acc) => RawTerm.PLam(name, acc) }
    }

  lazy val splitAtExpr: Parser[RawTerm] =
    kw("split@") ~> expr ~ (kw("with") ~> tok("{") ~> repsep(branch, tok(";")) <~ tok("}")) ^^ {
      case ty ~ branches =>
        val loc = freshLoc()
        RawTerm.Split("_splitAt_L" + loc.line + "_C" + loc.col, loc, ty, branches)
    }

  lazy val expr1: Parser[RawTerm] =
    piExpr | sigmaExpr | funOrExpr2

  lazy val piExpr: Parser[RawTerm] =
    icityTele ~ (tok("->") ~> expr1) ^^ {
      case tele ~ body => buildIcityBindsPi(tele, body)
    }

  lazy val sigmaExpr: Parser[RawTerm] =
    pathTele ~ (tok("*") ~> expr1) ^^ {
      case tele ~ body =>
        tele.foldRight(body) { case ((name, ty), acc) => RawTerm.Sigma(RawTerm.Lam(Icity.Explicit, name, ty, acc)) }
    }

  lazy val funOrExpr2: Parser[RawTerm] =
    expr2 ~ opt(tok("->") ~> expr1) ^^ {
      case e ~ None       => e
      case e ~ Some(body) => RawTerm.Pi(Icity.Explicit, RawTerm.Lam(Icity.Explicit, "_", e, body))
    }

  /**
   * Application and formula application level.
   *
   * Supports interleaved regular, implicit, and path application:
   * `f a {b} @ i x @ j` parses with correct icity annotations.
   *
   * Each "argument" is either:
   *   - a regular (explicit) term (`atomExpr`)
   *   - an implicit application (`{expr}`)
   *   - a path application (`@ formula`)
   */
  lazy val expr2: Parser[RawTerm] =
    atomExpr ~ rep(
      tok("{") ~> expr <~ tok("}") ^^ (arg => Left((Icity.Implicit, arg))) |
      atomExpr ^^ (arg => Left((Icity.Explicit, arg))) |
      tok("@") ~> formula ^^ (Right(_))
    ) ^^ {
      case head ~ args =>
        args.foldLeft(head) {
          case (acc, Left((icity, arg))) => RawTerm.App(icity, acc, arg)
          case (acc, Right(phi))         => RawTerm.AppFormula(acc, phi)
        }
    }

  lazy val atomExpr: Parser[RawTerm] =
    baseAtomExpr ~ rep(elem(".1", _ == ".1") | elem(".2", _ == ".2")) ^^ {
      case e ~ projs => projs.foldLeft(e) {
        case (acc, ".1") => RawTerm.Fst(acc)
        case (acc, ".2") => RawTerm.Snd(acc)
        case (acc, _)    => acc
      }
    }

  lazy val baseAtomExpr: Parser[RawTerm] =
    uExpr | pathPExpr | compExpr | fillExpr |
    glueTypeExpr | glueElemExpr | unglueElemExpr |
    idTypeExpr | idPairExpr | idJExpr |
    transportExpr | holeExpr | pairExpr | identExpr | parenExpr

  lazy val uExpr: Parser[RawTerm] = kw("U") ^^^ RawTerm.U

  lazy val pathPExpr: Parser[RawTerm] =
    kw("PathP") ~> atomExpr ~ atomExpr ~ atomExpr ^^ {
      case a ~ u ~ v => RawTerm.PathP(a, u, v)
    }

  lazy val compExpr: Parser[RawTerm] =
    kw("comp") ~> atomExpr ~ atomExpr ~ system ^^ {
      case ty ~ base ~ sys => RawTerm.Comp(ty, base, sys)
    }

  lazy val fillExpr: Parser[RawTerm] =
    kw("fill") ~> atomExpr ~ atomExpr ~ system ^^ {
      case ty ~ base ~ sys => RawTerm.Fill(ty, base, sys)
    }

  lazy val glueTypeExpr: Parser[RawTerm] =
    kw("Glue") ~> atomExpr ~ system ^^ {
      case base ~ sys => RawTerm.Glue(base, sys)
    }

  lazy val glueElemExpr: Parser[RawTerm] =
    kw("glue") ~> atomExpr ~ system ^^ {
      case base ~ sys => RawTerm.GlueElem(base, sys)
    }

  lazy val unglueElemExpr: Parser[RawTerm] =
    kw("unglue") ~> atomExpr ~ system ^^ {
      case base ~ sys => RawTerm.UnGlueElem(base, sys)
    }

  lazy val idTypeExpr: Parser[RawTerm] =
    kw("Id") ~> atomExpr ~ atomExpr ~ atomExpr ^^ {
      case ty ~ u ~ v => RawTerm.Id(ty, u, v)
    }

  lazy val idPairExpr: Parser[RawTerm] =
    kw("idC") ~> atomExpr ~ system ^^ {
      case w ~ sys => RawTerm.IdPair(w, sys)
    }

  lazy val idJExpr: Parser[RawTerm] =
    kw("idJ") ~> atomExpr ~ atomExpr ~ atomExpr ~ atomExpr ~ atomExpr ~ atomExpr ^^ {
      case a ~ t ~ c ~ d ~ x ~ p => RawTerm.IdJ(a, t, c, d, x, p)
    }

  lazy val transportExpr: Parser[RawTerm] =
    kw("transport") ~> atomExpr ~ atomExpr ^^ {
      case ty ~ base => RawTerm.Comp(ty, base, Map.empty)
    }

  lazy val holeExpr: Parser[RawTerm] =
    holeIdent ^^ { _ => RawTerm.Hole(freshLoc()) }

  lazy val pairExpr: Parser[RawTerm] =
    tok("(") ~> expr ~ (tok(",") ~> rep1sep(expr, tok(","))) <~ tok(")") ^^ {
      case e ~ es => (e :: es).reduceRight(RawTerm.Pair.apply)
    }

  lazy val identExpr: Parser[RawTerm] =
    ident >> { name =>
      (tok("{") ~> expr <~ tok("}") ^^ { arg => RawTerm.App(Icity.Implicit, RawTerm.Var(name), arg) }) |
      success(RawTerm.Var(name))
    }

  lazy val parenExpr: Parser[RawTerm] =
    tok("(") ~> expr <~ tok(")")

  def branch: Parser[RawBranch] =
    ident ~ rep(ident) >> { case ctor ~ args =>
      (tok("@") ~> rep1(ident) >> { dims =>
        tok("->") ~> expWhere ^^ { body =>
          RawBranch.PathBranch(ctor, args, dims, body)
        }
      }) |
      (tok("->") ~> expWhere ^^ { body => RawBranch.OrdinaryBranch(ctor, args, body) })
    }

  def expWhere: Parser[RawTerm] =
    expr ~ opt(kw("where") ~> tok("{") ~> rawDeclsBlock <~ tok("}")) ^^ {
      case e ~ None        => e
      case e ~ Some(decls) => RawTerm.Where(e, decls)
    }

  def rawDeclsBlock: Parser[List[RawDecl]] =
    repsep(rawDecl, tok(";"))

  def rawDecl: Parser[RawDecl] =
    rawDeclTransparentAll | rawDeclOpaque | rawDeclTransparent |
    rawDeclMutual | rawDeclData | rawDeclHData |
    rawDeclTyped

  lazy val rawDeclTyped: Parser[RawDecl] =
    ident ~ rawTele ~ (tok(":") ~> expr) ~ (tok("=") ~> rawDeclTypedRhs) ^^ {
      case name ~ tele ~ ty ~ rhs => rhs(name, tele, ty)
    }

  private def rawDeclTypedRhs: Parser[(String, List[(List[String], RawTerm)], RawTerm) => RawDecl] =
    (kw("split") ~> tok("{") ~> repsep(branch, tok(";")) <~ tok("}") ^^ {
      branches => (name: String, tele: List[(List[String], RawTerm)], ty: RawTerm) =>
        RawDecl.Split(name, tele, ty, branches)
    }) |
    (kw("undefined") ^^^ {
      (name: String, tele: List[(List[String], RawTerm)], ty: RawTerm) => RawDecl.Undef(name, tele, ty)
    }) |
    (rawExpWhere ^^ {
      body => (name: String, tele: List[(List[String], RawTerm)], ty: RawTerm) => RawDecl.Def(name, tele, ty, body)
    })

  def rawDeclData: Parser[RawDecl] =
    kw("data") ~> ident ~ rawTele ~ (tok("=") ~> repsep(rawLabel, tok("|"))) ^^ {
      case name ~ tele ~ labels => RawDecl.Data(name, tele, labels)
    }

  def rawDeclHData: Parser[RawDecl] =
    kw("hdata") ~> ident ~ rawTele ~ (tok("=") ~> repsep(rawLabel, tok("|"))) ^^ {
      case name ~ tele ~ labels => RawDecl.HData(name, tele, labels)
    }

  def rawDeclMutual: Parser[RawDecl] =
    kw("mutual") ~> tok("{") ~> repsep(rawDecl, tok(";")) <~ tok("}") ^^ {
      decls => RawDecl.Mutual(decls)
    }

  def rawDeclOpaque: Parser[RawDecl] =
    kw("opaque") ~> ident ^^ { name => RawDecl.Opaque(name) }

  def rawDeclTransparent: Parser[RawDecl] =
    kw("transparent") ~> ident ^^ { name => RawDecl.Transparent(name) }

  def rawDeclTransparentAll: Parser[RawDecl] =
    kw("transparent_all") ^^^ RawDecl.TransparentAll

  def rawExpWhere: Parser[RawExpWhere] =
    expr ~ opt(kw("where") ~> tok("{") ~> rawDeclsBlock <~ tok("}")) ^^ {
      case e ~ None        => RawExpWhere.NoWhere(e)
      case e ~ Some(decls) => RawExpWhere.Where(e, decls)
    }

  def rawTele: Parser[List[(List[String], RawTerm)]] =
    rep(tok("(") ~> rep1(ident) ~ (tok(":") ~> expr) <~ tok(")") ^^ {
      case names ~ ty => (names, ty)
    })

  def rawLabel: Parser[RawLabel] =
    ident ~ rawTele >> { case name ~ tele =>
      (tok("<") ~> rep1(ident) <~ tok(">")) ~ system ^^ {
        case dims ~ sys => RawLabel.PathLabel(name, tele, dims, sys)
      } | success(RawLabel.OrdinaryLabel(name, tele))
    }

  private def buildLams(tele: List[(String, RawTerm)], body: RawTerm): RawTerm =
    tele.foldRight(body) { case ((name, ty), acc) => RawTerm.Lam(Icity.Explicit, name, ty, acc) }

  private def buildBindsPi(tele: List[(String, RawTerm)], body: RawTerm): RawTerm =
    tele.foldRight(body) { case ((name, ty), acc) => RawTerm.Pi(Icity.Explicit, RawTerm.Lam(Icity.Explicit, name, ty, acc)) }

  private def buildIcityLams(tele: List[(Icity, String, RawTerm)], body: RawTerm): RawTerm =
    tele.foldRight(body) { case ((icity, name, ty), acc) => RawTerm.Lam(icity, name, ty, acc) }

  private def buildIcityBindsPi(tele: List[(Icity, String, RawTerm)], body: RawTerm): RawTerm =
    tele.foldRight(body) { case ((icity, name, ty), acc) => RawTerm.Pi(icity, RawTerm.Lam(icity, name, ty, acc)) }
}

/**
 * Public entry point for the two-phase parse pipeline.
 *
 * Phase 1 (this object): source text → `RawModule` / `RawTerm`.
 * Phase 2 (`Resolver`):  `RawModule` → `ParsedModule` / `Term`.
 *
 * `parseImports` performs only a minimal parse of the module header to
 * extract the module name and import list, without building a full `RawModule`.
 * This is used by the import loader to resolve dependencies before full parsing.
 */
object Parser {

  def parseImports(source: String): ParsedImports =
    new CubicalParser().parseImports(source)

  def parseRawModule(source: String): RawModule =
    new CubicalParser().parseRawModule(source)

  def parseRawExpression(source: String): RawTerm =
    new CubicalParser().parseRawExpression(source)
}
