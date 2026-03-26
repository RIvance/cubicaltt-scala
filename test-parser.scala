import cubical.Parser

@main def testParser() =
  val input = "data bool = false | true"
  println(s"Parsing: $input")
  Parser.parseModule(input) match {
    case Right(decls) => println(s"Success: $decls")
    case Left(err) => println(s"Error: $err")
  }
