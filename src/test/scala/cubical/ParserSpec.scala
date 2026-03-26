package cubical

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import java.io.File
import scala.io.Source

class ParserSpec extends AnyFlatSpec with Matchers {
  
  val examplesDir = new File("examples")
  val cttFiles = examplesDir.listFiles().filter(_.getName.endsWith(".ctt"))
  
  cttFiles.foreach { file =>
    s"Parser" should s"successfully parse ${file.getName}" in {
      val source = Source.fromFile(file)
      val content = try source.mkString finally source.close()
      
      val result = Parser.parseModule(content)
      
      result match {
        case Right(_) => succeed
        case Left(err) => fail(s"Parse error: $err")
      }
    }
  }
}
