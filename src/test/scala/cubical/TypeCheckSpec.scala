package cubical

import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import java.io.File
import scala.io.Source

class TypeCheckSpec extends AnyFlatSpec with Matchers {
  
  val examplesDir = new File("examples")
  val cttFiles = examplesDir.listFiles().filter(_.getName.endsWith(".ctt"))
  
  cttFiles.foreach { file =>
    s"Type checker" should s"successfully check ${file.getName}" in {
      val source = Source.fromFile(file)
      val content = try source.mkString finally source.close()
      
      // Parse
      val parseResult = Parser.parseModule(content)
      parseResult match {
        case Left(err) => fail(s"Parse error: $err")
        case Right(decls) =>
          // Convert to mutual decls format
          val mutualDecls = decls.map {
            case Decl.DefDecl(name, ty, body) => (name, (ty, body))
            case Decl.DataDecl(name, _, ty, _) => (name, (ty, Term.Var(name)))
          }
          
          // Type check
          val ctx = TCtx(Env.empty, Map.empty, Nil)
          val loc = Loc(file.getName, 1, 1)
          try {
            ctx.withDecls(loc, mutualDecls)
            succeed
          } catch {
            case e: Exception => fail(s"Type check error: ${e.getMessage}")
          }
      }
    }
  }
}
