package cubical

import org.scalatest.ParallelTestExecution
import org.scalatest.flatspec.AnyFlatSpec

import java.io.File
import scala.io.Source
import scala.util.Using

class TypeCheckSpec extends AnyFlatSpec with ParallelTestExecution {

  val exampleFiles: Array[File] = Option(new File("examples").listFiles())
    .getOrElse(Array.empty[File])
    .filter(f => f.isFile && f.getName.endsWith(".ctt"))
    .sortBy(_.getName)

  exampleFiles.foreach { file =>
    "Type checker" should s"successfully check ${file.getName}" in {
      println(s"Testing ${file.getName}...")
      val (_, _, modules) = TypeCheckSpec.loadModules(file.getPath)
      val allDecls = modules.flatMap(_.declarations)
      val (maybeErr, _) = TypeChecker.runDeclss(TEnv.silentEnv, allDecls)

      maybeErr match {
        case Some(err) => fail(s"Type check error: $err")
        case None => succeed
      }
    }
  }
}

object TypeCheckSpec {
  case class LoadedModule(
    name: String,
    declarations: List[Declarations],
    names: List[(Ident, SymKind)]
  )

  def readFile(file: File): String =
    Using.resource(Source.fromFile(file))(_.mkString)

  def loadModules(
    filePath: String,
    notOk: Set[String] = Set.empty,
    loaded: Set[String] = Set.empty,
    modules: List[LoadedModule] = Nil
  ): (Set[String], Set[String], List[LoadedModule]) = {
    if (notOk.contains(filePath)) {
      throw new RuntimeException(s"Looping imports in $filePath")
    }
    if (loaded.contains(filePath)) {
      return (notOk, loaded, modules)
    }

    val file = new File(filePath)
    if (!file.exists()) {
      throw new RuntimeException(s"$filePath does not exist")
    }

    val source = readFile(file)
    val expectedName = file.getName.stripSuffix(".ctt")

    val parsedImports = Parser.parseImports(source) match {
      case Left(err) => throw new RuntimeException(s"Parse failed in $filePath\n$err")
      case Right(pi) =>
        if (pi.name != expectedName) {
          throw new RuntimeException(
            s"Module name mismatch in $filePath: expected $expectedName, got ${pi.name}"
          )
        }
        pi
    }

    val parent = Option(file.getParentFile).getOrElse(new File("."))
    val importPaths = parsedImports.imports.map(imp => new File(parent, s"$imp.ctt").getPath)

    var currentNotOk = notOk + filePath
    var currentLoaded = loaded
    var currentModules = modules

    for (imp <- importPaths) {
      val (no, lo, mo) = loadModules(imp, currentNotOk, currentLoaded, currentModules)
      currentNotOk = no
      currentLoaded = lo
      currentModules = mo
    }

    val importedNames = currentModules.flatMap(_.names)

    Parser.parseModule(source, expectedName, importedNames) match {
      case Left(err) => throw new RuntimeException(s"Resolve failed in $filePath\n$err")
      case Right(parsed) => (
        notOk,
        currentLoaded + filePath,
        currentModules :+ LoadedModule(parsed.name, parsed.declarations, parsed.names)
      )
    }
  }
}