package cubical

import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.matchers.should.Matchers
import scala.io.Source

class ParserTest extends AnyFunSuite with Matchers {
  
  def parseFile(path: String): Either[String, List[Decl]] = {
    val source = Source.fromFile(path)
    try {
      val content = source.mkString
      Parser.parseModule(content)
    } finally {
      source.close()
    }
  }
  
  test("parse bool.ctt") {
    val result = parseFile("examples/bool.ctt")
    result match {
      case Left(err) => fail(s"Parse failed: $err")
      case Right(_) => succeed
    }
  }
  
  test("parse nat.ctt") {
    val result = parseFile("examples/nat.ctt")
    result match {
      case Left(err) => fail(s"Parse failed: $err")
      case Right(_) => succeed
    }
  }
}
