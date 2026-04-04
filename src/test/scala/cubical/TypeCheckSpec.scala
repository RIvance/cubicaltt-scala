package cubical

import org.scalatest.ParallelTestExecution
import org.scalatest.Tag
import org.scalatest.flatspec.AnyFlatSpec

import java.io.File
import scala.io.Source
import scala.util.Using

object Slow extends Tag("Slow")

class TypeCheckSpec extends AnyFlatSpec with ParallelTestExecution {

  private val examplesDir = new File("examples")
  private val slowDir = new File("examples/slow")

  private def cttFiles(dir: File): Array[File] =
    Option(dir.listFiles())
      .getOrElse(Array.empty[File])
      .filter(f => f.isFile && f.getName.endsWith(".ctt"))
      .sortBy(_.getName)

  private val searchDirs: List[File] = List(examplesDir, slowDir).filter(_.isDirectory)

  cttFiles(examplesDir).foreach { file =>
    "Type checker" should s"successfully check ${file.getName}" in {
      TypeCheckSpec.checkFile(file, searchDirs)
    }
  }

  cttFiles(slowDir).foreach { file =>
    "Type checker" should s"successfully check slow/${file.getName}" taggedAs Slow in {
      TypeCheckSpec.checkFile(file, searchDirs)
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

  def checkFile(file: File, searchDirs: List[File]): Unit = {
    val (_, _, modules) = loadModules(file.getPath, searchDirs = searchDirs)
    val allDecls = modules.flatMap(_.declarations)
    val (maybeErr, _) = Elaborator.elaborateDeclss(TypeEnv.empty, allDecls)
    maybeErr.foreach { err =>
      throw new AssertionError(s"Type check error: $err")
    }
  }

  def resolveImport(name: String, localDir: File, searchDirs: List[File]): File = {
    val localFile = new File(localDir, s"$name.ctt")
    if (localFile.exists()) localFile
    else {
      searchDirs
        .map(dir => new File(dir, s"$name.ctt"))
        .find(_.exists())
        .getOrElse(throw new RuntimeException(s"Cannot find import $name (searched ${localDir +: searchDirs})"))
    }
  }

  def loadModules(
    filePath: String,
    notOk: Set[String] = Set.empty,
    loaded: Set[String] = Set.empty,
    modules: List[LoadedModule] = Nil,
    searchDirs: List[File] = Nil
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

    val parsedImports = Parser.parseImports(source)
    if (parsedImports.name != expectedName) throw new RuntimeException(
      s"Module name mismatch in $filePath: expected $expectedName, got ${parsedImports.name}"
    )

    val parent = Option(file.getParentFile).getOrElse(new File("."))
    val importFiles = parsedImports.imports.map(imp => resolveImport(imp, parent, searchDirs))

    var currentNotOk = notOk + filePath
    var currentLoaded = loaded
    var currentModules = modules

    for (imp <- importFiles) {
      val (no, lo, mo) = loadModules(imp.getPath, currentNotOk, currentLoaded, currentModules, searchDirs)
      currentNotOk = no
      currentLoaded = lo
      currentModules = mo
    }

    val importedNames = currentModules.flatMap(_.names)

    val raw = Parser.parseRawModule(source)
    val parsed = Resolver.resolveModule(raw, importedNames)
    (notOk, currentLoaded + filePath, currentModules :+ LoadedModule(parsed.name, parsed.declarations, parsed.names))
  }
}
