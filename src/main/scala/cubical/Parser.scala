package cubical

import scala.util.parsing.combinator.*
import Term.*
import Decl.*

/** Parser for cubical type theory syntax.
 *  Compatible with Mortberg's grammar but with Unicode support.
 */
object Parser extends RegexParsers:
  
  // ── Lexical ──────────────────────────────────────────────
  
  override def skipWhitespace = true
  override protected val whiteSpace = """(\s|--.*)+""".r  // Handle comments
  
  val reserved = Set("data", "module", "where", "import", "U", "PathP", "comp", "fill", "Glue", "glue", "unglue", "split")
  
  def ident: Parser[String] = 
    """[a-zA-Z_][a-zA-Z0-9_']*""".r.filter(!reserved.contains(_))
  
  def number: Parser[Int] = 
    """[0-9]+""".r ^^ (_.toInt)
  
  // ── Terms ────────────────────────────────────────────────
  
  def term: Parser[Term] = expr
  
  def expr: Parser[Term] = 
    piType | sigmaType | pathType | lamExpr | app
  
  def piType: Parser[Term] =
    ("(" ~> ident <~ ":") ~ (term <~ ")") ~ ("->" ~> term) ^^ {
      case x ~ a ~ b => Pi(a, Lam(x, a, b))
    }
  
  def sigmaType: Parser[Term] =
    ("(" ~> ident <~ ":") ~ (term <~ ")") ~ ("*" ~> term) ^^ {
      case x ~ a ~ b => Sigma(a, Lam(x, a, b))
    }
  
  def pathType: Parser[Term] =
    "Path" ~> atom ~ atom ~ atom ^^ {
      case a ~ u ~ v => PathP(Lam("_", Univ, a), u, v)
    } |
    "PathP" ~> atom ~ atom ~ atom ^^ {
      case a ~ u ~ v => PathP(a, u, v)
    }
  
  def lamExpr: Parser[Term] =
    "\\" ~> rep1(ident) ~ ("->" ~> term) ^^ {
      case xs ~ body => xs.foldRight(body)((x, b) => Lam(x, Univ, b))
    }
  
  def app: Parser[Term] = 
    atom ~ rep(atom) ^^ {
      case f ~ args => args.foldLeft(f)(App.apply)
    }
  
  def atom: Parser[Term] =
    "U" ^^^ Univ |
    ident ^^ Var.apply |
    "(" ~> term <~ ")"
  
  // ── Declarations ─────────────────────────────────────────
  
  def moduleHeader: Parser[String] =
    "module" ~> ident <~ "where"
  
  def importDecl: Parser[Unit] =
    "import" ~> ident ^^^ ()
  
  def decl: Parser[Decl] =
    ("data" ~> ident) ~ ("=" ~> rep1(constructor)) ^^ {
      case name ~ constrs => DataDecl(name, Nil, Univ, constrs)
    } |
    (ident <~ ":") ~ (term <~ "=") ~ term ^^ {
      case name ~ ty ~ body => DefDecl(name, ty, body)
    }
  
  def constructor: Parser[(String, Term)] =
    opt("|") ~> ident ~ opt("(" ~> ident ~ (":" ~> term) <~ ")") ^^ {
      case name ~ Some(param ~ ty) => (name, ty)
      case name ~ None => (name, Univ)
    }
  
  def module: Parser[List[Decl]] = 
    opt(moduleHeader) ~> rep(importDecl) ~> rep(decl)
  
  // ── Public API ───────────────────────────────────────────
  
  def parseModule(input: String): Either[String, List[Decl]] =
    parseAll(module, input) match {
      case Success(result, _) => Right(result)
      case NoSuccess(msg, _) => Left(msg)
    }

end Parser

