package cubical

object DebugParser {
  def main(args: Array[String]): Unit = {
    val filePath = if (args.nonEmpty) args(0) else "examples/test_minimal.ctt"
    val source = scala.io.Source.fromFile(filePath).mkString

    println("=== Source ===")
    println(source)

    println("\n=== Tokens (raw) ===")
    val rawTokens = LayoutPreprocessor.tokenize(source)
    rawTokens.foreach(t => println(s"  ${t.line}:${t.col} '${t.text}'"))

    println("\n=== Tokens (with layout) ===")
    val tokens = LayoutPreprocessor.preprocess(source)
    println(tokens.mkString(" "))

    println("\n=== Parse result ===")
    val expectedName = new java.io.File(filePath).getName.stripSuffix(".ctt")
    Parser.parseModule(source, expectedName) match {
      case Left(err) => println(s"PARSE ERROR: $err")
      case Right(parsed) =>
        println(s"Module: ${parsed.name}")
        println(s"Imports: ${parsed.imports}")
        println(s"Declarations: ${parsed.declarations.length}")
        parsed.declarations.foreach(d => println(s"  $d"))
        println(s"Names: ${parsed.names}")
    }
  }
}
