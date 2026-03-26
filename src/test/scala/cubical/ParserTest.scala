package cubical

import munit.FunSuite
import Term.*

class ParserTest extends FunSuite:
  
  test("parse universe") {
    val result = Parser.parseAll(Parser.term, "U")
    assertEquals(result.get, Univ)
  }
  
  test("parse variable") {
    val result = Parser.parseAll(Parser.term, "x")
    assertEquals(result.get, Var("x"))
  }
  
  test("parse application") {
    val result = Parser.parseAll(Parser.term, "f x")
    assertEquals(result.get, App(Var("f"), Var("x")))
  }
  
  test("parse lambda") {
    val result = Parser.parseAll(Parser.term, "\\x -> x")
    assertEquals(result.get, Lam("x", Univ, Var("x")))
  }
  
  test("parse pi type") {
    val result = Parser.parseAll(Parser.term, "(x : U) -> U")
    assertEquals(result.get, Pi(Univ, Lam("x", Univ, Univ)))
  }

end ParserTest
