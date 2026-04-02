package cubical

import scala.util.parsing.combinator.*
import scala.collection.immutable.Map as IMap

object LayoutPreprocessor {

  private val layoutKeywords: Set[String] = Set("where", "let", "split", "mutual", "with")
  private val layoutStopKeywords: Set[String] = Set("in")

  case class PosToken(text: String, line: Int, col: Int)

  def tokenize(source: String): List[PosToken] = {
    val result = scala.collection.mutable.ListBuffer[PosToken]()
    val lines = source.split("\n", -1)
    var inBlockComment = 0
    var lineIdx = 0
    while (lineIdx < lines.length) {
      val lineText = lines(lineIdx)
      var col = 0
      var visualCol = 0
      while (col < lineText.length) {
        if (inBlockComment > 0) {
          if (col + 1 < lineText.length && lineText(col) == '-' && lineText(col + 1) == '}') {
            inBlockComment -= 1
            col += 2
            visualCol += 2
          } else if (col + 1 < lineText.length && lineText(col) == '{' && lineText(col + 1) == '-') {
            inBlockComment += 1
            col += 2
            visualCol += 2
          } else {
            if (lineText(col) == '\t') visualCol = (visualCol / 8 + 1) * 8
            else visualCol += 1
            col += 1
          }
        } else if (col + 1 < lineText.length && lineText(col) == '{' && lineText(col + 1) == '-') {
          inBlockComment += 1
          col += 2
          visualCol += 2
        } else if (col + 1 < lineText.length && lineText(col) == '-' && lineText(col + 1) == '-') {
          col = lineText.length
        } else if (lineText(col) == '\t') {
          visualCol = (visualCol / 8 + 1) * 8
          col += 1
        } else if (lineText(col).isWhitespace) {
          col += 1
          visualCol += 1
        } else {
          val startVisualCol = visualCol
          val tok = readToken(lineText, col)
          result += PosToken(tok, lineIdx + 1, startVisualCol + 1)
          col += tok.length
          visualCol += tok.length
        }
      }
      lineIdx += 1
    }
    result.toList
  }

  private def readToken(line: String, start: Int): String = {
    val c = line(start)
    if (start + 1 < line.length) {
      val two = line.substring(start, start + 2)
      two match {
        case "->" | "<=" | ">=" | "\\/" | "/\\" => return two
        case _ =>
      }
    }
    if ("(){}[],:;@\\*<>.?".contains(c)) {
      if (c == '.' && start + 1 < line.length && (line(start + 1) == '1' || line(start + 1) == '2')) {
        return line.substring(start, start + 2)
      }
      return c.toString
    }
    if (c == '!' ) {
      var i = start + 1
      while (i < line.length && line(i).isDigit) i += 1
      return line.substring(start, i)
    }
    if (c == '=' || c == '-') {
      return c.toString
    }
    val sb = new StringBuilder
    var i = start
    while (i < line.length && !line(i).isWhitespace && !"(){}[],:;@\\*<>\"".contains(line(i))) {
      if (i + 1 < line.length) {
        val pair = line.substring(i, i + 2)
        if (pair == "->" || pair == "/\\" || pair == "\\/") {
          if (i == start) return pair else return sb.toString
        }
      }
      if (line(i) == '.' && i != start) return sb.toString
      if (line(i) == '=' && i != start) return sb.toString
      if (line(i) == '-' && i != start) return sb.toString
      sb += line(i)
      i += 1
    }
    val result = sb.toString
    // Handle split@ as a single token (BNFC treats it as a keyword literal)
    if (result == "split" && i < line.length && line(i) == '@') {
      return "split@"
    }
    result
  }

  /*
   * BNFC layout algorithm:
   *   After a layout keyword, the next token's column becomes the block column.
   *   Tokens at that column get ; inserted before them.
   *   Tokens at a lesser column close the block with }.
   *   Layout stop keywords (e.g. "in") also close the current block.
   *   Explicit braces { } override layout for a block (tracked as column 0).
   */
  def insertLayout(tokens: List[PosToken]): List[String] = {
    val result = scala.collection.mutable.ListBuffer[String]()
    var layoutStack: List[Int] = Nil
    var expectLayout = false
    var i = 0

    while (i < tokens.length) {
      val tok = tokens(i)

      if (expectLayout) {
        expectLayout = false
        if (tok.text == "{") {
          result += tok.text
          layoutStack = 0 :: layoutStack
          i += 1
        } else {
          val blockCol = tok.col
          layoutStack = blockCol :: layoutStack
          result += "{"
          result += tok.text
          if (layoutKeywords.contains(tok.text)) expectLayout = true
          i += 1
        }
      } else {
        layoutStack match {
          case blockCol :: rest if blockCol > 0 =>
            if (layoutStopKeywords.contains(tok.text)) {
              // BNFC algorithm: stop keyword closes current block plus all
              // blocks below it that are more indented than the stop token
              result += "}"
              val (extraClose, remaining) = rest.span {
                case col if col > 0 => tok.col < col
                case _              => false
              }
              extraClose.foreach(_ => result += "}")
              layoutStack = remaining
              result += tok.text
              i += 1
            } else if (tok.col < blockCol) {
              result += "}"
              layoutStack = rest
            } else if (tok.col == blockCol && i > 0) {
              result += ";"
              result += tok.text
              if (layoutKeywords.contains(tok.text)) expectLayout = true
              i += 1
            } else if (tok.col < blockCol) {
              result += "}"
              layoutStack = rest
            } else {
              result += tok.text
              if (layoutKeywords.contains(tok.text)) expectLayout = true
              i += 1
            }
          case _ =>
            if (layoutStack.nonEmpty && layoutStack.head == 0 && tok.text == "}") {
              result += tok.text
              layoutStack = layoutStack.tail
              i += 1
            } else {
              result += tok.text
              if (layoutKeywords.contains(tok.text)) expectLayout = true
              i += 1
            }
        }
      }
    }

    while (layoutStack.nonEmpty) {
      if (layoutStack.head > 0) result += "}"
      layoutStack = layoutStack.tail
    }

    result.toList
  }

  def preprocess(source: String): List[String] = insertLayout(tokenize(source))
}

sealed trait SymKind
object SymKind {
  case object Variable extends SymKind
  case object Constructor extends SymKind
  case object PConstructor extends SymKind
  case object DimName extends SymKind
}

case class ResolverEnv(
  moduleName: String,
  variables: List[(Ident, SymKind)]
) {
  def insertIdent(name: Ident, kind: SymKind): ResolverEnv = {
    if (name == "_") this
    else copy(variables = (name, kind) :: variables)
  }

  def insertIdents(pairs: List[(Ident, SymKind)]): ResolverEnv =
    pairs.foldLeft(this)((env, pair) => env.insertIdent(pair._1, pair._2))

  def insertVar(name: Ident): ResolverEnv = insertIdent(name, SymKind.Variable)

  def insertVars(names: List[Ident]): ResolverEnv =
    names.foldLeft(this)((env, n) => env.insertVar(n))

  def insertName(name: Ident): ResolverEnv = insertIdent(name, SymKind.DimName)

  def insertNames(names: List[Ident]): ResolverEnv =
    names.foldLeft(this)((env, n) => env.insertName(n))

  def lookupKind(name: Ident): Option[SymKind] =
    variables.find(_._1 == name).map(_._2)
}

object ResolverEnv {
  val empty: ResolverEnv = ResolverEnv("", Nil)
}

object Parser extends RegexParsers {

  override def skipWhitespace: Boolean = true
  override val whiteSpace = "[ \t\r\n]+".r

  private var locCounter: Int = 0
  private def freshLoc(): Loc = {
    locCounter += 1
    Loc("", locCounter, 0)
  }

  private def kw(s: String): Parser[String] =
    if (s.last.isLetterOrDigit || s.last == '_' || s.last == '\'') {
      regex(s"\\Q$s\\E(?![a-zA-Z0-9_'])".r)
    } else {
      literal(s)
    }

  private val keywords: Set[String] = Set(
    "module", "where", "let", "in", "split", "with", "mutual",
    "import", "data", "hdata", "undefined", "PathP", "comp",
    "transport", "fill", "Glue", "glue", "unglue", "U",
    "opaque", "transparent", "transparent_all", "Id", "idC", "idJ",
    "split@"
  )

  def ident: Parser[String] = {
    val standard = "[a-zA-Z_][a-zA-Z0-9_']*".r
    val bangIdent = "![0-9]*".r
    (standard | bangIdent).filter(s => !keywords.contains(s))
  }

  def holeIdent: Parser[String] = literal("?")

  // ---- Mutable resolver environment ----
  // Pragmatic approach: mutable state with save/restore at scope boundaries,
  // since scala-parser-combinators use backtracking.

  private var resolverEnv: ResolverEnv = ResolverEnv.empty
  private var rawMode: Boolean = false

  private def withScopedEnv[A](modify: ResolverEnv => ResolverEnv)(p: => Parser[A]): Parser[A] = {
    Parser { input =>
      val saved = resolverEnv
      resolverEnv = modify(saved)
      val result = p(input)
      resolverEnv = saved
      result
    }
  }

  private def resolveVar(name: Ident): Either[String, Term] = {
    if (rawMode) return Right(Term.Var(name))
    resolverEnv.lookupKind(name) match {
      case Some(SymKind.Variable)     => Right(Term.Var(name))
      case Some(SymKind.Constructor)  => Right(Term.Con(name, Nil))
      case Some(SymKind.PConstructor) => Left(s"Path constructor $name used as variable (needs type in curly braces)")
      case Some(SymKind.DimName)      => Left(s"Name $name used as variable")
      case None                       => Left(s"Cannot resolve variable $name in module ${resolverEnv.moduleName}")
    }
  }

  private def resolveName(name: Ident): Either[String, Name] = {
    if (rawMode) return Right(Name(name))
    resolverEnv.lookupKind(name) match {
      case Some(SymKind.DimName) => Right(Name(name))
      case _                     => Left(s"Cannot resolve name $name in module ${resolverEnv.moduleName}")
    }
  }

  // ---- Formula parsers ----

  def dir: Parser[Dir] =
    literal("0") ^^^ Dir.Zero | literal("1") ^^^ Dir.One

  def formula: Parser[Formula] = formulaDisj

  def formulaDisj: Parser[Formula] =
    formulaConj ~ rep(literal("\\/") ~> formulaConj) ^^ {
      case f ~ fs => fs.foldLeft(f)(Formula.orFormula)
    }

  def formulaConj: Parser[Formula] =
    formulaAtom ~ rep(literal("/\\") ~> formulaAtom) ^^ {
      case f ~ fs => fs.foldLeft(f)(Formula.andFormula)
    }

  def formulaAtom: Parser[Formula] =
    literal("-") ~> formulaAtom ^^ Formula.negFormula |
    dir ^^ { d => Formula.Dir(d) } |
    ident >> { name =>
      resolveName(name) match {
        case Right(n)  => success(Formula.Atom(n))
        case Left(err) => failure(err)
      }
    } |
    literal("(") ~> formula <~ literal(")")

  // ---- System parsers ----

  def face: Parser[(Name, Dir)] =
    literal("(") ~> ident ~ (literal("=") ~> dir) <~ literal(")") >> {
      case name ~ d => resolveName(name) match {
        case Right(n)  => success((n, d))
        case Left(err) => failure(err)
      }
    }

  def faceMap: Parser[Face] = rep(face) ^^ { _.toMap }

  def side: Parser[(Face, Term)] =
    faceMap ~ (literal("->") ~> expr) ^^ { case alpha ~ e => (alpha, e) }

  def system: Parser[System[Term]] =
    literal("[") ~> repsep(side, literal(",")) <~ literal("]") ^^ { _.toMap }

  // ---- Telescope parsers ----

  def teleEntry: Parser[List[(Ident, Term)]] =
    literal("(") ~> rep1(ident) ~ (literal(":") ~> expr) <~ literal(")") ^^ {
      case names ~ ty => names.map(n => (n, ty))
    }

  def telescope: Parser[List[(Ident, Term)]] = rep(teleEntry) ^^ { _.flatten }

  def pTeleEntry: Parser[List[(Ident, Term)]] =
    literal("(") ~> expr ~ (literal(":") ~> expr) <~ literal(")") >> {
      case e ~ ty =>
        appsToIdents(e) match {
          case Some(ids) => success(ids.map(id => (id, ty)))
          case None      => failure("malformed ptele")
        }
    }

  def pTele: Parser[List[(Ident, Term)]] = rep1(pTeleEntry) ^^ { _.flatten }

  private def appsToIdents(e: Term): Option[List[Ident]] = {
    val (head, args) = Term.unApps(e)
    (head :: args).map {
      case Term.Var(x) => Some(x)
      case _           => None
    }.sequence
  }

  private implicit class OptionListOps[A](val xs: List[Option[A]]) {
    def sequence: Option[List[A]] =
      xs.foldRight(Option(List.empty[A])) {
        case (Some(a), Some(acc)) => Some(a :: acc)
        case _                    => None
      }
  }

  // ---- Expression parsers (precedence levels 0-5) ----

  def expr: Parser[Term] = expr0

  def expr0: Parser[Term] = letExpr | lamExpr | plamExpr | splitAtExpr | expr1

  def letExpr: Parser[Term] =
    kw("let") ~> literal("{") ~> rawDeclsBlock ~ (literal("}") ~> kw("in") ~> expr) >> {
      case rawDecls ~ body =>
        if (rawMode) {
          // In raw mode, don't resolve — build Where chain with raw (unresolved) decls
          val rawWhere = rawDeclsToWheres(rawDecls, body)
          success(rawWhere)
        } else {
          resolveDecls(rawDecls) match {
            case Right((resolvedDecls, names)) =>
              withScopedEnv(_.insertIdents(names))(success(Term.mkWheres(resolvedDecls, body)))
            case Left(err) => failure(err)
          }
        }
    }

  def lamExpr: Parser[Term] =
    literal("\\") ~> pTele ~ (literal("->") ~> expr) ^^ {
      case tele ~ body => buildLams(tele, body)
    }

  def plamExpr: Parser[Term] = {
    literal("<") ~> rep1(ident) >> { names =>
      withScopedEnv(_.insertNames(names)) {
        literal(">") ~> expr ^^ { body => buildPLams(names, body) }
      }
    }
  }

  def splitAtExpr: Parser[Term] =
    kw("split@") ~> expr ~ (kw("with") ~> literal("{") ~> repsep(branch, literal(";")) <~ literal("}")) ^^ {
      case ty ~ branches =>
        val loc = freshLoc()
        Term.Split(resolverEnv.moduleName + "_L" + loc.line + "_C" + loc.col, loc, ty, branches)
    }

  def expr1: Parser[Term] = piExpr | sigmaExpr | funOrExpr2

  def piExpr: Parser[Term] =
    pTele ~ (literal("->") ~> expr1) ^^ {
      case tele ~ body => buildBinds(Term.Pi.apply, tele, body)
    }

  def sigmaExpr: Parser[Term] =
    pTele ~ (literal("*") ~> expr1) ^^ {
      case tele ~ body => buildBinds(Term.Sigma.apply, tele, body)
    }

  def funOrExpr2: Parser[Term] =
    expr2 ~ opt(literal("->") ~> expr1) ^^ {
      case a ~ Some(b) => Term.Pi(Term.Lam("_", a, b))
      case a ~ None    => a
    }

  def expr2: Parser[Term] =
    expr3 ~ rep(appArg) ^^ {
      case head ~ args =>
        args.foldLeft(head) {
          case (acc, Left(arg))  => Term.mkApps(acc, List(arg))
          case (acc, Right(phi)) => Term.AppFormula(acc, phi)
        }
    }

  def appArg: Parser[Either[Term, Formula]] =
    literal("@") ~> formula ^^ { phi => Right(phi) } |
    expr3 ^^ { e => Left(e) }

  def expr3: Parser[Term] =
    pathPExpr | compExpr | hCompExpr | transExpr | fillExpr |
    glueExpr | glueElemExpr | unGlueElemExpr |
    idExpr | idPairExpr | idJExpr |
    expr4

  def pathPExpr: Parser[Term] =
    kw("PathP") ~> expr4 ~ expr4 ~ expr4 ^^ { case a ~ u ~ v => Term.PathP(a, u, v) }

  def compExpr: Parser[Term] =
    kw("comp") ~> expr4 ~ expr4 ~ system ^^ { case u ~ v ~ sys => Term.Comp(u, v, sys) }

  def hCompExpr: Parser[Term] =
    kw("hComp") ~> expr4 ~ expr4 ~ system ^^ { case u ~ v ~ sys => Term.HComp(u, v, sys) }

  def transExpr: Parser[Term] =
    kw("transport") ~> expr4 ~ expr4 ^^ { case u ~ v => Term.Comp(u, v, IMap.empty) }

  def fillExpr: Parser[Term] =
    kw("fill") ~> expr4 ~ expr4 ~ system ^^ { case u ~ v ~ sys => Term.Fill(u, v, sys) }

  def glueExpr: Parser[Term] =
    kw("Glue") ~> expr4 ~ system ^^ { case u ~ sys => Term.Glue(u, sys) }

  def glueElemExpr: Parser[Term] =
    kw("glue") ~> expr4 ~ system ^^ { case u ~ sys => Term.GlueElem(u, sys) }

  def unGlueElemExpr: Parser[Term] =
    kw("unglue") ~> expr4 ~ system ^^ { case u ~ sys => Term.UnGlueElem(u, sys) }

  def idExpr: Parser[Term] =
    kw("Id") ~> expr4 ~ expr4 ~ expr3 ^^ { case a ~ u ~ v => Term.Id(a, u, v) }

  def idPairExpr: Parser[Term] =
    kw("idC") ~> expr4 ~ system ^^ { case u ~ sys => Term.IdPair(u, sys) }

  def idJExpr: Parser[Term] =
    kw("idJ") ~> expr4 ~ expr4 ~ expr4 ~ expr4 ~ expr4 ~ expr4 ^^ {
      case a ~ t ~ c ~ d ~ x ~ p => Term.IdJ(a, t, c, d, x, p)
    }

  def expr4: Parser[Term] =
    expr5 ~ rep(literal(".1") | literal(".2")) ^^ {
      case e ~ projs =>
        projs.foldLeft(e) {
          case (acc, ".1") => Term.Fst(acc)
          case (acc, ".2") => Term.Snd(acc)
          case (acc, _)    => acc
        }
    }

  def expr5: Parser[Term] =
    uExpr | holeExpr | pairExpr | identExpr | parenExpr

  def uExpr: Parser[Term] = kw("U") ^^^ Term.U

  def holeExpr: Parser[Term] = holeIdent ^^ { _ => Term.Hole(freshLoc()) }

  def pairExpr: Parser[Term] =
    literal("(") ~> expr ~ (literal(",") ~> rep1sep(expr, literal(","))) <~ literal(")") ^^ {
      case e ~ es => (e :: es).reduceRight(Term.Pair.apply)
    }

  // Combined parser for ident-based expressions: PCon (ident { expr }) or Var (ident)
  // Must parse ident once and then branch, to avoid committing on ident in pconExpr
  // and failing to backtrack to varExpr.
  def identExpr: Parser[Term] =
    ident >> { name =>
      (literal("{") ~> expr <~ literal("}") ^^ { ty => Term.PCon(name, ty, Nil, Nil) }) |
      (resolveVar(name) match {
        case Right(term) => success(term)
        case Left(err)   => failure(err)
      })
    }

  def parenExpr: Parser[Term] = literal("(") ~> expr <~ literal(")")

  // ---- Branch parsers ----

  def branch: Parser[Branch] =
    ident ~ rep(ident) >> { case ctor ~ args =>
      (literal("@") ~> rep1(ident) >> { dims =>
        withScopedEnv(_.insertNames(dims).insertVars(args)) {
          literal("->") ~> expWhere ^^ { body =>
            Branch.PBranch(ctor, args, dims.map(Name.apply), body)
          }
        }
      }) |
      withScopedEnv(_.insertVars(args)) {
        literal("->") ~> expWhere ^^ { body => Branch.OBranch(ctor, args, body) }
      }
    }

  def expWhere: Parser[Term] =
    expr ~ opt(kw("where") ~> literal("{") ~> rawDeclsBlock <~ literal("}")) ^^ {
      case e ~ None => e
      case e ~ Some(rawDecls) =>
        if (rawMode) {
          rawDeclsToWheres(rawDecls, e)
        } else {
          resolveDecls(rawDecls) match {
            case Right((resolvedDecls, _)) => Term.mkWheres(resolvedDecls, e)
            case Left(_)                   => e
          }
        }
    }

  // ---- Raw (unresolved) declaration types ----

  sealed trait RawDecl
  case class RawDeclDef(name: Ident, tele: List[(List[Ident], Term)], ty: Term, body: RawExpWhere) extends RawDecl
  case class RawDeclData(name: Ident, tele: List[(List[Ident], Term)], labels: List[RawLabel]) extends RawDecl
  case class RawDeclHData(name: Ident, tele: List[(List[Ident], Term)], labels: List[RawLabel]) extends RawDecl
  case class RawDeclSplit(name: Ident, tele: List[(List[Ident], Term)], ty: Term, branches: List[Branch]) extends RawDecl
  case class RawDeclUndef(name: Ident, tele: List[(List[Ident], Term)], ty: Term) extends RawDecl
  case class RawDeclMutual(decls: List[RawDecl]) extends RawDecl
  case class RawDeclOpaque(name: Ident) extends RawDecl
  case class RawDeclTransparent(name: Ident) extends RawDecl
  case object RawDeclTransparentAll extends RawDecl

  sealed trait RawExpWhere
  case class RawWhere(expr: Term, decls: List[RawDecl]) extends RawExpWhere
  case class RawNoWhere(expr: Term) extends RawExpWhere

  sealed trait RawLabel
  case class RawOLabel(name: Ident, tele: List[(List[Ident], Term)]) extends RawLabel
  case class RawPLabel(name: Ident, tele: List[(List[Ident], Term)], dims: List[Ident], sys: System[Term]) extends RawLabel

  // ---- Raw declaration parsers ----

  def rawDeclsBlock: Parser[List[RawDecl]] = Parser { input =>
    val savedRawMode = rawMode
    rawMode = true
    val result = repsep(rawDecl, literal(";"))(input)
    rawMode = savedRawMode
    result
  }

  def rawDecl: Parser[RawDecl] =
    rawDeclTransparentAll | rawDeclOpaque | rawDeclTransparent |
    rawDeclMutual | rawDeclData | rawDeclHData |
    rawDeclTyped

  // Combined parser for declarations sharing prefix: ident ~ rawTele ~ ":" ~ expr ~ "="
  // Branches after "=" into: split { ... }, undefined, or regular definition
  def rawDeclTyped: Parser[RawDecl] =
    ident ~ rawTele ~ (literal(":") ~> expr) ~ (literal("=") ~> rawDeclTypedRhs) ^^ {
      case name ~ tele ~ ty ~ rhs => rhs(name, tele, ty)
    }

  private def rawDeclTypedRhs: Parser[(Ident, List[(List[Ident], Term)], Term) => RawDecl] =
    (kw("split") ~> literal("{") ~> repsep(branch, literal(";")) <~ literal("}") ^^ {
      branches => (name: Ident, tele: List[(List[Ident], Term)], ty: Term) => RawDeclSplit(name, tele, ty, branches)
    }) |
    (kw("undefined") ^^^ {
      (name: Ident, tele: List[(List[Ident], Term)], ty: Term) => RawDeclUndef(name, tele, ty)
    }) |
    (rawExpWhere ^^ {
      body => (name: Ident, tele: List[(List[Ident], Term)], ty: Term) => RawDeclDef(name, tele, ty, body)
    })

  def rawDeclData: Parser[RawDeclData] =
    kw("data") ~> ident ~ rawTele ~ (literal("=") ~> repsep(rawLabel, literal("|"))) ^^ {
      case name ~ tele ~ labels => RawDeclData(name, tele, labels)
    }

  def rawDeclHData: Parser[RawDeclHData] =
    kw("hdata") ~> ident ~ rawTele ~ (literal("=") ~> repsep(rawLabel, literal("|"))) ^^ {
      case name ~ tele ~ labels => RawDeclHData(name, tele, labels)
    }

  def rawDeclMutual: Parser[RawDeclMutual] =
    kw("mutual") ~> literal("{") ~> repsep(rawDecl, literal(";")) <~ literal("}") ^^ {
      decls => RawDeclMutual(decls)
    }

  def rawDeclOpaque: Parser[RawDeclOpaque] =
    kw("opaque") ~> ident ^^ { name => RawDeclOpaque(name) }

  def rawDeclTransparent: Parser[RawDeclTransparent] =
    kw("transparent") ~> ident ^^ { name => RawDeclTransparent(name) }

  def rawDeclTransparentAll: Parser[RawDeclTransparentAll.type] =
    kw("transparent_all") ^^^ RawDeclTransparentAll

  def rawExpWhere: Parser[RawExpWhere] =
    expr ~ opt(kw("where") ~> literal("{") ~> rawDeclsBlock <~ literal("}")) ^^ {
      case e ~ None        => RawNoWhere(e)
      case e ~ Some(decls) => RawWhere(e, decls)
    }

  def rawTele: Parser[List[(List[Ident], Term)]] =
    rep(literal("(") ~> rep1(ident) ~ (literal(":") ~> expr) <~ literal(")") ^^ {
      case names ~ ty => (names, ty)
    })

  def rawLabel: Parser[RawLabel] =
    ident ~ rawTele >> { case name ~ tele =>
      (literal("<") ~> rep1(ident) <~ literal(">")) ~ system ^^ {
        case dims ~ sys => RawPLabel(name, tele, dims, sys)
      } | success(RawOLabel(name, tele))
    }

  // ---- Declaration resolution ----

  private def flattenRawTele(tele: List[(List[Ident], Term)]): List[(Ident, Term)] =
    tele.flatMap { case (names, ty) => names.map(n => (n, ty)) }

  private def resolveDecls(rawDecls: List[RawDecl]): Either[String, (List[Declarations], List[(Ident, SymKind)])] =
    rawDecls.foldLeft(Right((List.empty[Declarations], List.empty[(Ident, SymKind)])): Either[String, (List[Declarations], List[(Ident, SymKind)])]) {
      case (Left(err), _) => Left(err)
      case (Right((accDecls, accNames)), d) =>
        resolveDecl(d) match {
          case Right((decl, names)) =>
            resolverEnv = resolverEnv.insertIdents(names)
            Right((accDecls :+ decl, accNames ++ names))
          case Left(err) => Left(err)
        }
    }

  private def resolveDecl(d: RawDecl): Either[String, (Declarations, List[(Ident, SymKind)])] = d match {
    case RawDeclDef(name, rawTele, ty, body) =>
      val tele = flattenRawTele(rawTele)
      for {
        rType <- resolveBindsPi(tele, ty)
        rBody <- resolveDefBody(name, tele, body)
      } yield {
        val loc = freshLoc()
        (Declarations.MutualDecls(loc, List((name, (rType, rBody)))), List((name, SymKind.Variable)))
      }

    case RawDeclData(name, rawTele, rawLabels) =>
      resolveDeclData(name, rawTele, rawLabels, useHSum = false)

    case RawDeclHData(name, rawTele, rawLabels) =>
      resolveDeclData(name, rawTele, rawLabels, useHSum = true)

    case RawDeclSplit(name, rawTele, ty, branches) =>
      val tele = flattenRawTele(rawTele)
      val loc = freshLoc()
      val splitName = resolverEnv.moduleName + "_L" + loc.line + "_C" + loc.col
      for {
        rType <- resolveBindsPi(tele, ty)
        rTy <- withResolverScope(_.insertVars(tele.map(_._1)))(resolveTerm(ty))
        rBranches <- withResolverScope(_.insertVars(name :: tele.map(_._1)))(resolveBranches(branches))
        rTele <- resolveTelescope(tele)
      } yield {
        val body = buildLams(rTele, Term.Split(splitName, loc, rTy, rBranches))
        (Declarations.MutualDecls(loc, List((name, (rType, body)))), List((name, SymKind.Variable)))
      }

    case RawDeclUndef(name, rawTele, ty) =>
      val tele = flattenRawTele(rawTele)
      for {
        rType <- resolveBindsPi(tele, ty)
      } yield {
        val loc = freshLoc()
        (Declarations.MutualDecls(loc, List((name, (rType, Term.Undef(loc, rType))))), List((name, SymKind.Variable)))
      }

    case RawDeclMutual(rawDecls) =>
      val allNames = rawDecls.flatMap(extractDeclNames)
      withResolverScope(_.insertIdents(allNames)) {
        val results = rawDecls.map(resolveNonMutualDecl)
        val errors = results.collect { case Left(err) => err }
        if (errors.nonEmpty) Left(errors.head)
        else {
          val pairs = results.flatMap(_.toOption.toList.flatten)
          val loc = freshLoc()
          Right((Declarations.MutualDecls(loc, pairs), allNames))
        }
      }

    case RawDeclOpaque(name) =>
      Right((Declarations.OpaqueDecl(name), Nil))

    case RawDeclTransparent(name) =>
      Right((Declarations.TransparentDecl(name), Nil))

    case RawDeclTransparentAll =>
      Right((Declarations.TransparentAllDecl, Nil))
  }

  private def resolveBindsPi(tele: Telescope, body: Term): Either[String, Term] =
    tele match {
      case Nil => resolveTerm(body)
      case (name, ty) :: rest =>
        for {
          rTy <- resolveTerm(ty)
          rInner <- withResolverScope(_.insertVar(name))(resolveBindsPi(rest, body))
        } yield Term.Pi(Term.Lam(name, rTy, rInner))
    }

  private def resolveLams(tele: Telescope, body: Term): Either[String, Term] =
    tele match {
      case Nil => resolveTerm(body)
      case (name, ty) :: rest =>
        for {
          rTy <- resolveTerm(ty)
          rInner <- withResolverScope(_.insertVar(name))(resolveLams(rest, body))
        } yield Term.Lam(name, rTy, rInner)
    }

  private def resolveDefBody(name: Ident, tele: Telescope, body: RawExpWhere): Either[String, Term] = {
    val bodyTerm = body match {
      case RawNoWhere(e) => e
      case RawWhere(e, decls) =>
        withResolverScope(_.insertVars(name :: tele.map(_._1))) {
          resolveDecls(decls) match {
            case Right((resolvedDecls, _)) => Right(Term.mkWheres(resolvedDecls, e))
            case Left(err) => Left(err)
          }
        } match {
          case Right(t) => t
          case Left(err) => return Left(err)
        }
    }
    withResolverScope(_.insertVar(name)) {
      resolveLams(tele, bodyTerm)
    }
  }

  private def resolveDeclData(
    name: Ident,
    rawTele: List[(List[Ident], Term)],
    rawLabels: List[RawLabel],
    useHSum: Boolean
  ): Either[String, (Declarations, List[(Ident, SymKind)])] = {
    val tele = flattenRawTele(rawTele)
    val loc = freshLoc()

    val cs = rawLabels.collect { case RawOLabel(lbl, _) => (lbl, SymKind.Constructor: SymKind) }
    val pcs = rawLabels.collect { case RawPLabel(lbl, _, _, _) => (lbl, SymKind.PConstructor: SymKind) }
    val sumCtor = if (!useHSum && pcs.isEmpty) Term.Sum.apply else Term.HSum.apply

    val rawLabelsResolved = rawLabels.map {
      case RawOLabel(lbl, rawLabelTele) =>
        Label.OLabel(lbl, flattenRawTele(rawLabelTele))
      case RawPLabel(lbl, rawLabelTele, dims, sys) =>
        Label.PLabel(lbl, flattenRawTele(rawLabelTele), dims.map(Name.apply), sys)
    }

    for {
      rType <- resolveBindsPi(tele, Term.U)
      rBody <- withResolverScope(_.insertVar(name)) {
        resolveLabelsWithLams(tele, cs ++ pcs, rawLabelsResolved, loc, name, sumCtor)
      }
    } yield {
      val names = (name, SymKind.Variable: SymKind) :: (cs ++ pcs)
      (Declarations.MutualDecls(loc, List((name, (rType, rBody)))), names)
    }
  }

  private def resolveLabelsWithLams(
    tele: Telescope,
    ctors: List[(Ident, SymKind)],
    labels: List[Label],
    loc: Loc,
    name: Ident,
    sumCtor: (Loc, Ident, List[Label]) => Term
  ): Either[String, Term] =
    tele match {
      case Nil =>
        withResolverScope(_.insertIdents(ctors)) {
          resolveLabels(labels).map(rLabels => sumCtor(loc, name, rLabels))
        }
      case (paramName, ty) :: rest =>
        for {
          rTy <- resolveTerm(ty)
          rInner <- withResolverScope(_.insertVar(paramName)) {
            resolveLabelsWithLams(rest, ctors, labels, loc, name, sumCtor)
          }
        } yield Term.Lam(paramName, rTy, rInner)
    }

  private def extractDeclNames(d: RawDecl): List[(Ident, SymKind)] = d match {
    case RawDeclDef(name, _, _, _)     => List((name, SymKind.Variable))
    case RawDeclData(name, _, labels)  =>
      (name, SymKind.Variable: SymKind) :: labels.map {
        case RawOLabel(lbl, _)       => (lbl, SymKind.Constructor: SymKind)
        case RawPLabel(lbl, _, _, _) => (lbl, SymKind.PConstructor: SymKind)
      }
    case RawDeclHData(name, _, labels) =>
      (name, SymKind.Variable: SymKind) :: labels.map {
        case RawOLabel(lbl, _)       => (lbl, SymKind.Constructor: SymKind)
        case RawPLabel(lbl, _, _, _) => (lbl, SymKind.PConstructor: SymKind)
      }
    case RawDeclSplit(name, _, _, _)   => List((name, SymKind.Variable))
    case RawDeclUndef(name, _, _)      => List((name, SymKind.Variable))
    case RawDeclMutual(decls)          => decls.flatMap(extractDeclNames)
    case RawDeclOpaque(_)              => Nil
    case RawDeclTransparent(_)         => Nil
    case RawDeclTransparentAll         => Nil
  }

  private def resolveNonMutualDecl(d: RawDecl): Either[String, List[Declaration]] = d match {
    case RawDeclDef(name, rawTele, ty, body) =>
      val tele = flattenRawTele(rawTele)
      for {
        rType <- resolveBindsPi(tele, ty)
        rBody <- resolveDefBody(name, tele, body)
      } yield List((name, (rType, rBody)))

    case RawDeclData(name, rawTele, rawLabels) =>
      val tele = flattenRawTele(rawTele)
      val loc = freshLoc()
      val cs = rawLabels.collect { case RawOLabel(lbl, _) => (lbl, SymKind.Constructor: SymKind) }
      val pcs = rawLabels.collect { case RawPLabel(lbl, _, _, _) => (lbl, SymKind.PConstructor: SymKind) }
      val sumCtor = if (pcs.isEmpty) Term.Sum.apply else Term.HSum.apply
      val rawLabelsResolved = rawLabels.map {
        case RawOLabel(lbl, rawLabelTele) => Label.OLabel(lbl, flattenRawTele(rawLabelTele))
        case RawPLabel(lbl, rawLabelTele, dims, sys) => Label.PLabel(lbl, flattenRawTele(rawLabelTele), dims.map(Name.apply), sys)
      }
      for {
        rType <- resolveBindsPi(tele, Term.U)
        rBody <- withResolverScope(_.insertVar(name)) {
          resolveLabelsWithLams(tele, cs ++ pcs, rawLabelsResolved, loc, name, sumCtor)
        }
      } yield List((name, (rType, rBody)))

    case RawDeclHData(name, rawTele, rawLabels) =>
      val tele = flattenRawTele(rawTele)
      val loc = freshLoc()
      val cs = rawLabels.collect { case RawOLabel(lbl, _) => (lbl, SymKind.Constructor: SymKind) }
      val pcs = rawLabels.collect { case RawPLabel(lbl, _, _, _) => (lbl, SymKind.PConstructor: SymKind) }
      val rawLabelsResolved = rawLabels.map {
        case RawOLabel(lbl, rawLabelTele) => Label.OLabel(lbl, flattenRawTele(rawLabelTele))
        case RawPLabel(lbl, rawLabelTele, dims, sys) => Label.PLabel(lbl, flattenRawTele(rawLabelTele), dims.map(Name.apply), sys)
      }
      for {
        rType <- resolveBindsPi(tele, Term.U)
        rBody <- withResolverScope(_.insertVar(name)) {
          resolveLabelsWithLams(tele, cs ++ pcs, rawLabelsResolved, loc, name, Term.HSum.apply)
        }
      } yield List((name, (rType, rBody)))

    case RawDeclSplit(name, rawTele, ty, branches) =>
      val tele = flattenRawTele(rawTele)
      val loc = freshLoc()
      val splitName = resolverEnv.moduleName + "_L" + loc.line + "_C" + loc.col
      for {
        rType <- resolveBindsPi(tele, ty)
        rTy <- withResolverScope(_.insertVars(tele.map(_._1)))(resolveTerm(ty))
        rBranches <- withResolverScope(_.insertVars(name :: tele.map(_._1)))(resolveBranches(branches))
        rTele <- resolveTelescope(tele)
      } yield List((name, (rType, buildLams(rTele, Term.Split(splitName, loc, rTy, rBranches)))))

    case RawDeclUndef(name, rawTele, ty) =>
      val tele = flattenRawTele(rawTele)
      for {
        rType <- resolveBindsPi(tele, ty)
      } yield {
        val loc = freshLoc()
        List((name, (rType, Term.Undef(loc, rType))))
      }

    case _ => Right(Nil)
  }

  private def resolveTerm(t: Term): Either[String, Term] = {
    val (head, args) = Term.unApps(t)
    head match {
      case Term.Var(x) =>
        resolverEnv.lookupKind(x) match {
          case Some(SymKind.Variable) =>
            for { rArgs <- resolveArgs(args) } yield {
              if (rArgs.isEmpty) Term.Var(x)
              else Term.mkApps(Term.Var(x), rArgs)
            }
          case Some(SymKind.Constructor) =>
            for { rArgs <- resolveArgs(args) } yield Term.Con(x, rArgs)
          case Some(SymKind.PConstructor) =>
            Left(s"Path constructor $x used without curly braces for the type")
          case Some(SymKind.DimName) =>
            Left(s"Name $x used as expression")
          case None =>
            Left(s"Cannot resolve variable $x in module ${resolverEnv.moduleName}")
        }
      case _ =>
        for {
          rHead <- resolveTermInner(head)
          rArgs <- resolveArgs(args)
        } yield {
          if (rArgs.isEmpty) rHead
          else Term.mkApps(rHead, rArgs)
        }
    }
  }

  private def resolveArgs(args: List[Term]): Either[String, List[Term]] =
    args.foldRight(Right(Nil): Either[String, List[Term]]) { (a, acc) =>
      for { as <- acc; ra <- resolveTerm(a) } yield ra :: as
    }

  private def unAppsFormulas(t: Term): (Term, List[Term], List[Formula]) = {
    def collectFormulas(e: Term, phis: List[Formula]): (Term, List[Term], List[Formula]) = e match {
      case Term.AppFormula(u, phi) => collectFormulas(u, phi :: phis)
      case _ =>
        val (base, args) = unApps(e, Nil)
        (base, args, phis)
    }
    collectFormulas(t, Nil)
  }

  private def unApps(t: Term, acc: List[Term]): (Term, List[Term]) = t match {
    case Term.App(u, v) => unApps(u, v :: acc)
    case _              => (t, acc)
  }

  private def resolveTermInner(t: Term): Either[String, Term] = t match {
    case Term.U => Right(Term.U)
    case Term.Var(x) => resolveTerm(t)
    case Term.App(f, a) => resolveTerm(t)
    case Term.Pi(body) => resolveTermInner(body).map(Term.Pi.apply)
    case Term.Sigma(body) => resolveTermInner(body).map(Term.Sigma.apply)
    case Term.Lam(name, ty, body) =>
      for {
        rTy <- resolveTerm(ty)
        rBody <- withResolverScope(_.insertVar(name))(resolveTerm(body))
      } yield Term.Lam(name, rTy, rBody)
    case Term.Pair(a, b) =>
      for { ra <- resolveTerm(a); rb <- resolveTerm(b) } yield Term.Pair(ra, rb)
    case Term.Fst(p) => resolveTerm(p).map(Term.Fst.apply)
    case Term.Snd(p) => resolveTerm(p).map(Term.Snd.apply)
    case Term.Where(body, decls) =>
      resolveDeclarations(decls).flatMap { case (rDecls, names) =>
        withResolverScope(_.insertIdents(names))(resolveTerm(body)).map(rb => Term.Where(rb, rDecls))
      }
    case Term.Con(name, args) =>
      resolveArgs(args).map(rArgs => Term.Con(name, rArgs))
    case Term.PCon(name, dt, args, phis) =>
      for {
        rDt <- resolveTerm(dt)
        rArgs <- resolveArgs(args)
        rPhis <- resolveFormulas(phis)
      } yield Term.PCon(name, rDt, rArgs, rPhis)
    case Term.Split(name, loc, ty, branches) =>
      for {
        rTy <- resolveTerm(ty)
        rBranches <- resolveBranches(branches)
      } yield Term.Split(name, loc, rTy, rBranches)
    case Term.Sum(loc, name, labels) =>
      resolveLabels(labels).map(rLabels => Term.Sum(loc, name, rLabels))
    case Term.HSum(loc, name, labels) =>
      resolveLabels(labels).map(rLabels => Term.HSum(loc, name, rLabels))
    case Term.Undef(loc, ty) =>
      resolveTerm(ty).map(rTy => Term.Undef(loc, rTy))
    case Term.Hole(loc) => Right(Term.Hole(loc))
    case Term.PathP(a, u, v) =>
      for { ra <- resolveTerm(a); ru <- resolveTerm(u); rv <- resolveTerm(v) } yield Term.PathP(ra, ru, rv)
    case Term.PLam(dim, body) =>
      withResolverScope(_.insertName(dim.value))(resolveTerm(body)).map(rb => Term.PLam(dim, rb))
    case Term.AppFormula(_, _) =>
      // Flatten AppFormula chain: (((u v1) .. vn) phi1) .. phim -> (u, [v1,..,vn], [phi1,..,phim])
      // If base is PCon, merge formulas into the PCon node (matching Haskell's unAppsFormulas)
      val (base, args, phis) = unAppsFormulas(t)
      base match {
        case Term.PCon(name, dt, pcArgs, _) =>
          val allArgs = pcArgs ::: args
          for {
            rDt   <- resolveTerm(dt)
            rArgs <- resolveArgs(allArgs)
            rPhis <- phis.foldRight(Right(Nil): Either[String, List[Formula]]) { (f, acc) =>
              for { fs <- acc; rf <- resolveFormula(f) } yield rf :: fs
            }
          } yield Term.PCon(name, rDt, rArgs, rPhis)
        case _ =>
          for {
            rBase <- resolveTerm(base)
            rArgs <- resolveArgs(args)
            rPhis <- phis.foldRight(Right(Nil): Either[String, List[Formula]]) { (f, acc) =>
              for { fs <- acc; rf <- resolveFormula(f) } yield rf :: fs
            }
          } yield {
            val withArgs = if (rArgs.isEmpty) rBase else Term.mkApps(rBase, rArgs)
            rPhis.foldLeft(withArgs) { (acc, phi) => Term.AppFormula(acc, phi) }
          }
      }
    case Term.Comp(ty, base, sys) =>
      for { rTy <- resolveTerm(ty); rBase <- resolveTerm(base); rSys <- resolveSystemTerm(sys) } yield Term.Comp(rTy, rBase, rSys)
    case Term.Fill(ty, base, sys) =>
      for { rTy <- resolveTerm(ty); rBase <- resolveTerm(base); rSys <- resolveSystemTerm(sys) } yield Term.Fill(rTy, rBase, rSys)
    case Term.HComp(ty, base, sys) =>
      for { rTy <- resolveTerm(ty); rBase <- resolveTerm(base); rSys <- resolveSystemTerm(sys) } yield Term.HComp(rTy, rBase, rSys)
    case Term.Glue(base, sys) =>
      for { rBase <- resolveTerm(base); rSys <- resolveSystemTerm(sys) } yield Term.Glue(rBase, rSys)
    case Term.GlueElem(base, sys) =>
      for { rBase <- resolveTerm(base); rSys <- resolveSystemTerm(sys) } yield Term.GlueElem(rBase, rSys)
    case Term.UnGlueElem(base, sys) =>
      for { rBase <- resolveTerm(base); rSys <- resolveSystemTerm(sys) } yield Term.UnGlueElem(rBase, rSys)
    case Term.Id(ty, u, v) =>
      for { rTy <- resolveTerm(ty); ru <- resolveTerm(u); rv <- resolveTerm(v) } yield Term.Id(rTy, ru, rv)
    case Term.IdPair(w, sys) =>
      for { rW <- resolveTerm(w); rSys <- resolveSystemTerm(sys) } yield Term.IdPair(rW, rSys)
    case Term.IdJ(a, t, c, d, x, p) =>
      for {
        ra <- resolveTerm(a); rt <- resolveTerm(t); rc <- resolveTerm(c)
        rd <- resolveTerm(d); rx <- resolveTerm(x); rp <- resolveTerm(p)
      } yield Term.IdJ(ra, rt, rc, rd, rx, rp)
  }

  private def resolveFormula(phi: Formula): Either[String, Formula] = phi match {
    case Formula.Dir(d) => Right(Formula.Dir(d))
    case Formula.Atom(Name(x)) =>
      resolverEnv.lookupKind(x) match {
        case Some(SymKind.DimName) => Right(Formula.Atom(Name(x)))
        case _ => Left(s"Cannot resolve name $x in module ${resolverEnv.moduleName}")
      }
    case Formula.NegAtom(Name(x)) =>
      resolverEnv.lookupKind(x) match {
        case Some(SymKind.DimName) => Right(Formula.NegAtom(Name(x)))
        case _ => Left(s"Cannot resolve name $x in module ${resolverEnv.moduleName}")
      }
    case Formula.And(a, b) =>
      for { ra <- resolveFormula(a); rb <- resolveFormula(b) } yield Formula.And(ra, rb)
    case Formula.Or(a, b) =>
      for { ra <- resolveFormula(a); rb <- resolveFormula(b) } yield Formula.Or(ra, rb)
  }

  private def resolveFormulas(phis: List[Formula]): Either[String, List[Formula]] =
    phis.foldRight(Right(Nil): Either[String, List[Formula]]) { (phi, acc) =>
      for { as <- acc; rPhi <- resolveFormula(phi) } yield rPhi :: as
    }

  private def resolveSystemTerm(sys: System[Term]): Either[String, System[Term]] = {
    val entries = sys.toList
    entries.foldRight(Right(Map.empty[Face, Term]): Either[String, System[Term]]) { case ((face, term), acc) =>
      for {
        rAcc <- acc
        rFace <- resolveFace(face)
        rTerm <- resolveTerm(term)
      } yield rAcc + (rFace -> rTerm)
    }
  }

  private def resolveFace(face: Face): Either[String, Face] = {
    val entries = face.toList
    entries.foldRight(Right(Map.empty[Name, Dir]): Either[String, Face]) { case ((Name(x), d), acc) =>
      for {
        rAcc <- acc
        _ <- resolverEnv.lookupKind(x) match {
          case Some(SymKind.DimName) => Right(())
          case _ => Left(s"Cannot resolve name $x in face constraint in module ${resolverEnv.moduleName}")
        }
      } yield rAcc + (Name(x) -> d)
    }
  }

  private def resolveBranches(branches: List[Branch]): Either[String, List[Branch]] =
    branches.foldRight(Right(Nil): Either[String, List[Branch]]) { (b, acc) =>
      for { bs <- acc; rb <- resolveBranch(b) } yield rb :: bs
    }

  private def resolveBranch(b: Branch): Either[String, Branch] = b match {
    case Branch.OBranch(ctor, vars, body) =>
      withResolverScope(_.insertVars(vars))(resolveTerm(body)).map(rb => Branch.OBranch(ctor, vars, rb))
    case Branch.PBranch(ctor, vars, dims, body) =>
      withResolverScope(_.insertNames(dims.map(_.value)).insertVars(vars))(resolveTerm(body))
        .map(rb => Branch.PBranch(ctor, vars, dims, rb))
  }

  private def resolveLabels(labels: List[Label]): Either[String, List[Label]] =
    labels.foldRight(Right(Nil): Either[String, List[Label]]) { (l, acc) =>
      for { ls <- acc; rl <- resolveLabel(l) } yield rl :: ls
    }

  private def resolveLabel(l: Label): Either[String, Label] = l match {
    case Label.OLabel(name, tele) =>
      resolveTelescope(tele).map(rt => Label.OLabel(name, rt))
    case Label.PLabel(name, tele, dims, sys) =>
      for {
        rt <- resolveTelescope(tele)
        rSys <- withResolverScope(env => {
          val withNames = env.insertNames(dims.map(_.value))
          val withVars = withNames.insertVars(tele.map(_._1))
          withVars
        })(resolveSystemTerm(sys))
      } yield Label.PLabel(name, rt, dims, rSys)
  }

  private def resolveTelescope(tele: Telescope): Either[String, Telescope] =
    tele match {
      case Nil => Right(Nil)
      case (name, ty) :: rest =>
        for {
          rTy <- resolveTerm(ty)
          rRest <- withResolverScope(_.insertVar(name))(resolveTelescope(rest))
        } yield (name, rTy) :: rRest
    }

  private def withResolverScope[A](modify: ResolverEnv => ResolverEnv)(action: => Either[String, A]): Either[String, A] = {
    val saved = resolverEnv
    resolverEnv = modify(saved)
    val result = action
    resolverEnv = saved
    result
  }

  private def resolveDeclarations(decl: Declarations): Either[String, (Declarations, List[(Ident, SymKind)])] =
    decl match {
      case Declarations.MutualDecls(loc, pairs) =>
        val names = pairs.map { case (name, _) => (name, SymKind.Variable: SymKind) }
        withResolverScope(_.insertIdents(names)) {
          pairs.foldRight(Right(Nil): Either[String, List[Declaration]]) { case ((name, (ty, body)), acc) =>
            for {
              as <- acc
              rTy <- resolveTerm(ty)
              rBody <- resolveTerm(body)
            } yield (name, (rTy, rBody)) :: as
          }
        }.map(rPairs => (Declarations.MutualDecls(loc, rPairs), names))

      case Declarations.OpaqueDecl(name) =>
        Right((Declarations.OpaqueDecl(name), Nil))

      case Declarations.TransparentDecl(name) =>
        Right((Declarations.TransparentDecl(name), Nil))

      case Declarations.TransparentAllDecl =>
        Right((Declarations.TransparentAllDecl, Nil))
    }

  // ---- Term building helpers ----

  private def buildLams(tele: List[(Ident, Term)], body: Term): Term =
    tele.foldRight(body) { case ((name, ty), acc) => Term.Lam(name, ty, acc) }

  private def buildPLams(names: List[Ident], body: Term): Term =
    names.foldRight(body) { (name, acc) => Term.PLam(Name(name), acc) }

  private def buildBinds(f: Term => Term, tele: List[(Ident, Term)], body: Term): Term =
    tele.foldRight(body) { case ((name, ty), acc) => f(Term.Lam(name, ty, acc)) }

  private def buildBindsPi(tele: List[(Ident, Term)], body: Term): Term =
    buildBinds(Term.Pi.apply, tele, body)

  private def rawDeclsToWheres(rawDecls: List[RawDecl], body: Term): Term =
    rawDecls.foldRight(body) { (rd, acc) =>
      val decl = rawDeclToUnresolved(rd)
      Term.Where(acc, decl)
    }

  private def rawDeclToUnresolved(rd: RawDecl): Declarations = rd match {
    case RawDeclDef(name, rawTele, ty, rawBody) =>
      val tele = flattenRawTele(rawTele)
      val rType = buildBindsPi(tele, ty)
      val bodyTerm = rawBody match {
        case RawNoWhere(e)      => e
        case RawWhere(e, decls) => rawDeclsToWheres(decls, e)
      }
      val rBody = buildLams(tele, bodyTerm)
      Declarations.MutualDecls(freshLoc(), List((name, (rType, rBody))))

    case RawDeclSplit(name, rawTele, ty, branches) =>
      val tele = flattenRawTele(rawTele)
      val loc = freshLoc()
      val splitName = resolverEnv.moduleName + "_L" + loc.line + "_C" + loc.col
      val rType = buildBindsPi(tele, ty)
      val rBody = buildLams(tele, Term.Split(splitName, loc, ty, branches))
      Declarations.MutualDecls(loc, List((name, (rType, rBody))))

    case RawDeclUndef(name, rawTele, ty) =>
      val tele = flattenRawTele(rawTele)
      val loc = freshLoc()
      val rType = buildBindsPi(tele, ty)
      Declarations.MutualDecls(loc, List((name, (rType, Term.Undef(loc, rType)))))

    case RawDeclData(name, rawTele, rawLabels) =>
      val tele = flattenRawTele(rawTele)
      val loc = freshLoc()
      val labels = rawLabels.map {
        case RawOLabel(lbl, rawLabelTele) => Label.OLabel(lbl, flattenRawTele(rawLabelTele))
        case RawPLabel(lbl, rawLabelTele, dims, sys) => Label.PLabel(lbl, flattenRawTele(rawLabelTele), dims.map(Name.apply), sys)
      }
      val rType = buildBindsPi(tele, Term.U)
      val rBody = buildLams(tele, Term.Sum(loc, name, labels))
      Declarations.MutualDecls(loc, List((name, (rType, rBody))))

    case RawDeclHData(name, rawTele, rawLabels) =>
      val tele = flattenRawTele(rawTele)
      val loc = freshLoc()
      val labels = rawLabels.map {
        case RawOLabel(lbl, rawLabelTele) => Label.OLabel(lbl, flattenRawTele(rawLabelTele))
        case RawPLabel(lbl, rawLabelTele, dims, sys) => Label.PLabel(lbl, flattenRawTele(rawLabelTele), dims.map(Name.apply), sys)
      }
      val rType = buildBindsPi(tele, Term.U)
      val rBody = buildLams(tele, Term.HSum(loc, name, labels))
      Declarations.MutualDecls(loc, List((name, (rType, rBody))))

    case RawDeclMutual(decls) =>
      val pairs = decls.flatMap { rd =>
        rawDeclToUnresolved(rd) match {
          case Declarations.MutualDecls(_, ds) => ds
          case _ => Nil
        }
      }
      Declarations.MutualDecls(freshLoc(), pairs)

    case RawDeclOpaque(name)      => Declarations.OpaqueDecl(name)
    case RawDeclTransparent(name) => Declarations.TransparentDecl(name)
    case RawDeclTransparentAll    => Declarations.TransparentAllDecl
  }

  // ---- Module parser ----

  case class ParsedModule(
    name: String,
    imports: List[String],
    declarations: List[Declarations],
    names: List[(Ident, SymKind)]
  )

  def imp: Parser[String] = kw("import") ~> ident

  private def impOrDecl: Parser[Either[String, RawDecl]] =
    imp ^^ { i => Left(i) } | rawDecl ^^ { d => Right(d) }

  def moduleParser: Parser[ParsedModule] =
    kw("module") ~> ident ~ (kw("where") ~> literal("{") ~> impsAndDeclsBlock <~ literal("}")) ^^ {
      case name ~ (imports, rawDecls) =>
        resolverEnv = resolverEnv.copy(moduleName = name)
        resolveDecls(rawDecls) match {
          case Right((decls, names)) => ParsedModule(name, imports, decls, names)
          case Left(err)             => throw new RuntimeException(s"Resolver failed: $err")
        }
    }

  private def impsAndDeclsBlock: Parser[(List[String], List[RawDecl])] = Parser { input =>
    val savedRawMode = rawMode
    rawMode = true
    val result = repsep(impOrDecl, literal(";"))(input)
    rawMode = savedRawMode
    result.map { items =>
      val imports = items.collect { case Left(i) => i }
      val decls = items.collect { case Right(d) => d }
      (imports, decls)
    }
  }

  // ---- Public API ----

  case class ParsedImports(name: String, imports: List[String])

  private def moduleImportsParser: Parser[ParsedImports] =
    kw("module") ~> ident ~ (kw("where") ~> literal("{") ~> rep(imp <~ literal(";"))) ^^ {
      case name ~ imps => ParsedImports(name, imps)
    }

  def parseImports(source: String): Either[String, ParsedImports] = {
    val tokens = LayoutPreprocessor.preprocess(source)
    val tokenString = tokens.mkString(" ")
    parse(moduleImportsParser, tokenString) match {
      case Success(result, _)   => Right(result)
      case Failure(msg, next)   => Left(s"Parse error at position ${next.pos}: $msg")
      case Error(msg, next)     => Left(s"Parse error at position ${next.pos}: $msg")
    }
  }

  def parseModule(
    source: String,
    moduleName: String = "",
    existingNames: List[(Ident, SymKind)] = Nil
  ): Either[String, ParsedModule] = {
    locCounter = 0
    resolverEnv = ResolverEnv(moduleName, existingNames)
    val tokens = LayoutPreprocessor.preprocess(source)
    val tokenString = tokens.mkString(" ")
    parseAll(moduleParser, tokenString) match {
      case Success(result, _)   => Right(result)
      case Failure(msg, next)   => Left(s"Parse error at position ${next.pos}: $msg")
      case Error(msg, next)     => Left(s"Parse error at position ${next.pos}: $msg")
    }
  }

  def parseExpression(
    source: String,
    names: List[(Ident, SymKind)] = Nil
  ): Either[String, Term] = {
    locCounter = 0
    resolverEnv = ResolverEnv("", names)
    val tokens = LayoutPreprocessor.preprocess(source)
    val tokenString = tokens.mkString(" ")
    parseAll(expr, tokenString) match {
      case Success(result, _)   => Right(result)
      case Failure(msg, next)   => Left(s"Parse error at position ${next.pos}: $msg")
      case Error(msg, next)     => Left(s"Parse error at position ${next.pos}: $msg")
    }
  }
}
