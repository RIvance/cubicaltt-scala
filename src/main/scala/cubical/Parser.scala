package cubical

import scala.util.parsing.combinator.*
import Term.*
import Formula.*

/** Parser for cubical type theory syntax.
 *  Compatible with Mortberg's grammar but with Unicode support.
 */
object Parser extends RegexParsers:
  
  // ── Lexical ──────────────────────────────────────────────
  
  override def skipWhitespace = true
  
  def ident: Parser[String] = 
    """[a-zA-Z_][a-zA-Z0-9_']*""".r
  
  def number: Parser[Int] = 
    """[0-9]+""".r ^^ (_.toInt)
  
  // ── Terms ────────────────────────────────────────────────
  
  def term: Parser[Term] = expr
  
  def expr: Parser[Term] = 
    piType | sigmaType | pathType | lamExpr | app
  
  def piType: Parser[Term] =
    ("(" ~> ident <~ ":" ~ ")") ~ term ~ ("->" ~> term) ^^ {
      case x ~ a ~ b => Pi(Lam(x, a, b), a)
    } |
    "Π" ~> "(" ~> ident ~ (":" ~> term) ~ (")" ~> term) ^^ {
      case x ~ a ~ b => Pi(Lam(x, a, b), a)
    }
  
  def sigmaType: Parser[Term] =
    ("(" ~> ident <~ ":" ~ ")") ~ term ~ ("×" | "*") ~ term ^^ {
      case x ~ a ~ _ ~ b => Sigma(a, Lam(x, a, b))
    } |
    "Σ" ~> "(" ~> ident ~ (":" ~> term) ~ (")" ~> term) ^^ {
      case x ~ a ~ b => Sigma(a, Lam(x, a, b))
    }
  
  def pathType: Parser[Term] =
    "PathP" ~> "(" ~> term ~ (")" ~> term) ~ term ^^ {
      case a ~ u ~ v => PathP(a, u, v)
    }
  
  def lamExpr: Parser[Term] =
    ("\\" | "λ") ~> ident ~ (":" ~> term) ~ ("->" ~> term) ^^ {
      case x ~ ty ~ body => Lam(x, ty, body)
    }
  
  def app: Parser[Term] = 
    atom ~ rep(atom) ^^ {
      case f ~ args => args.foldLeft(f)(App.apply)
    }
  
  def atom: Parser[Term] =
    "U" ^^^ Univ |
    ident ^^ Var.apply |
    "(" ~> term <~ ")"

end Parser
