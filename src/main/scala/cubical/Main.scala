package cubical

import scala.io.Source
import java.io.File
import scala.util.{Try, Success, Failure}

object Main {

  case class Options(
    verbose: Boolean = true,
    batch: Boolean = false,
    time: Boolean = false
  )

  def main(args: Array[String]): Unit = {
    var options = Options()
    var files = List.empty[String]

    var helpOrVersion = false
    args.foreach {
      case "-d" | "--debug"   => options = options.copy(verbose = true)
      case "-b" | "--batch"   => options = options.copy(batch = true)
      case "-t" | "--time"    => options = options.copy(time = true)
      case "--help"           => printUsage(); helpOrVersion = true
      case "--version"        => println("cubicaltt-scala 0.1.0"); helpOrVersion = true
      case f                  => files = files :+ f
    }
    if (helpOrVersion) return

    files match {
      case Nil =>
        println("cubicaltt-scala — Cubical Type Theory in Scala 3")
        println("Usage: cubicaltt [options] <file.ctt>")
        println("  --help     print help")
        println("  --version  print version")
        println("  -d         debug/verbose mode")
        println("  -b         batch mode (no REPL)")
        println("  -t         measure time")
      case f :: Nil =>
        println(s"cubicaltt-scala — Loading $f")
        initLoop(options, f)
      case _ =>
        println("Error: expected zero or one file")
        printUsage()
    }
  }

  private def printUsage(): Unit = {
    println("Usage: cubicaltt [options] <file.ctt>")
    println("  --help     print help")
    println("  --version  print version")
    println("  -d         debug/verbose mode")
    println("  -b         batch mode (no REPL)")
    println("  -t         measure time")
  }

  case class LoadedModule(
    name: String,
    declarations: List[Declarations],
    names: List[(Ident, SymKind)]
  )

  def imports(
    verbose: Boolean,
    notOk: Set[String],
    loaded: Set[String],
    modules: List[LoadedModule],
    filePath: String
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

    val prefix = Option(file.getParent).map(_ + File.separator).getOrElse("")
    val source = Source.fromFile(file).mkString
    val expectedName = file.getName.stripSuffix(".ctt")

    val parsedImports = Parser.parseImports(source) match {
      case Left(err) =>
        throw new RuntimeException(s"Parse failed in $filePath\n$err")
      case Right(pi) =>
        if (pi.name != expectedName) {
          throw new RuntimeException(
            s"Module name mismatch in $filePath: expected $expectedName, got ${pi.name}"
          )
        }
        pi
    }

    val importPaths = parsedImports.imports.map(imp => prefix + imp + ".ctt")
    var currentNotOk = notOk + filePath
    var currentLoaded = loaded
    var currentModules = modules

    for (imp <- importPaths) {
      val (no, lo, mo) = imports(verbose, currentNotOk, currentLoaded, currentModules, imp)
      currentNotOk = no
      currentLoaded = lo
      currentModules = mo
    }

    val importedNames = currentModules.flatMap(_.names)

    Parser.parseModule(source, expectedName, importedNames) match {
      case Left(err) =>
        throw new RuntimeException(s"Resolve failed in $filePath\n$err")
      case Right(parsed) =>
        if (verbose) println(s"Parsed $filePath successfully!")
        (
          notOk,
          currentLoaded + filePath,
          currentModules :+ LoadedModule(parsed.name, parsed.declarations, parsed.names)
        )
    }
  }

  private def initLoop(options: Options, filePath: String): Unit = {
    try {
      val (_, _, modules) = imports(
        options.verbose,
        Set.empty,
        Set.empty,
        Nil,
        filePath
      )

      val allDecls = modules.flatMap(_.declarations)
      val allNames = modules.flatMap(_.names)

      val duplicates = allNames.map(_._1).groupBy(identity).collect { case (k, v) if v.size > 1 => k }.toList
      if (duplicates.nonEmpty) {
        println(s"Warning: the following definitions were shadowed [${duplicates.mkString(", ")}]")
      }

      val startEnv = if (options.verbose) TEnv.verboseEnv else TEnv.silentEnv
      val (merr, tenv) = TypeChecker.runDeclss(startEnv, allDecls)
      merr match {
        case Some(err) => println(s"Type checking failed: $err")
        case None =>
          if (modules.nonEmpty) println("File loaded.")
      }

      if (!options.batch) {
        repl(options, filePath, allNames, tenv)
      }
    } catch {
      case e: Exception =>
        println(s"Exception: ${e.getMessage}")
    }
  }

  private def repl(
    options: Options,
    filePath: String,
    names: List[(Ident, SymKind)],
    tenv: TEnv
  ): Unit = {
    val reader = new java.io.BufferedReader(new java.io.InputStreamReader(System.in))
    print("> ")
    var line = reader.readLine()
    while (line != null) {
      line.trim match {
        case ":q" => return
        case ":h" => printHelp()
        case ":r" => initLoop(options, filePath); return
        case s if s.startsWith(":l ") =>
          val newFile = s.drop(3).trim
          initLoop(options, newFile)
          return
        case s if s.startsWith(":n ") =>
          evalLine(s.drop(3).trim, names, tenv, normalize = true)
        case "" =>
        case s =>
          evalLine(s, names, tenv, normalize = false)
      }
      print("> ")
      line = reader.readLine()
    }
  }

  private def evalLine(
    input: String,
    names: List[(Ident, SymKind)],
    tenv: TEnv,
    normalize: Boolean
  ): Unit = {
    Parser.parseExpression(input, names) match {
      case Left(err) =>
        println(s"Parse error: $err")
      case Right(body) =>
        TypeChecker.runInfer(tenv, body) match {
          case Left(err) =>
            println(s"Could not type-check: $err")
          case Right(_) =>
            try {
              val e = Eval.eval(body, tenv.env)
              val result = if (normalize) Eval.normal(Nil, e) else e
              val prefix = if (normalize) "NORMEVAL: " else "EVAL: "
              println(s"$prefix$result")
            } catch {
              case ex: Exception =>
                println(s"Exception: ${ex.getMessage}")
            }
        }
    }
  }

  private def printHelp(): Unit = {
    println(
      """
        |Available commands:
        |  <statement>     infer type and evaluate statement
        |  :n <statement>  normalize statement
        |  :q              quit
        |  :l <filename>   loads filename (and resets environment)
        |  :r              reload
        |  :h              display this message
      """.stripMargin.trim
    )
  }
}
