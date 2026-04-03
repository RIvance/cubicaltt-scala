package cubical

/**
 * Layout preprocessor for the `.ctt` file format.
 *
 * The `.ctt` syntax uses Haskell/Agda-style layout: after certain *layout
 * keywords* the next token's column becomes the *block column*, and the
 * preprocessor inserts `{`, `}`, and `;` tokens to make the grammar
 * context-free for the downstream parser.
 *
 * Pipeline: `source  →  tokenize  →  insertLayout  →  List[String]`
 *
 * The resulting token list is fed to `CubicalParser` via a `TokenReader`.
 */
object LayoutPreprocessor {

  private val layoutKeywords: Set[String] = Set("where", "let", "split", "mutual", "with")
  private val layoutStopKeywords: Set[String] = Set("in")

  case class PosToken(text: String, line: Int, col: Int)

  def tokenize(source: String): List[PosToken] = {
    val result = scala.collection.mutable.ListBuffer[PosToken]()
    val lines = source.split("\n", -1)
    var inBlockComment = 0
    var lineIdx = 0
    while (lineIdx < lines.length) {
      val lineText = lines(lineIdx)
      var col = 0
      var visualCol = 0
      while (col < lineText.length) {
        if (inBlockComment > 0) {
          if (col + 1 < lineText.length && lineText(col) == '-' && lineText(col + 1) == '}') {
            inBlockComment -= 1
            col += 2
            visualCol += 2
          } else if (col + 1 < lineText.length && lineText(col) == '{' && lineText(col + 1) == '-') {
            inBlockComment += 1
            col += 2
            visualCol += 2
          } else {
            if (lineText(col) == '\t') visualCol = (visualCol / 8 + 1) * 8
            else visualCol += 1
            col += 1
          }
        } else if (col + 1 < lineText.length && lineText(col) == '{' && lineText(col + 1) == '-') {
          inBlockComment += 1
          col += 2
          visualCol += 2
        } else if (col + 1 < lineText.length && lineText(col) == '-' && lineText(col + 1) == '-') {
          col = lineText.length
        } else if (lineText(col) == '\t') {
          visualCol = (visualCol / 8 + 1) * 8
          col += 1
        } else if (lineText(col).isWhitespace) {
          col += 1
          visualCol += 1
        } else {
          val startVisualCol = visualCol
          val tok = readToken(lineText, col)
          result += PosToken(tok, lineIdx + 1, startVisualCol + 1)
          col += tok.length
          visualCol += tok.length
        }
      }
      lineIdx += 1
    }
    result.toList
  }

  private def readToken(line: String, start: Int): String = {
    val c = line(start)
    if (start + 1 < line.length) {
      val two = line.substring(start, start + 2)
      two match {
        case "->" | "<=" | ">=" | "\\/" | "/\\" => return two
        case _ =>
      }
    }
    if ("(){}[],:;@\\*<>.?".contains(c)) {
      if (c == '.' && start + 1 < line.length && (line(start + 1) == '1' || line(start + 1) == '2')) {
        return line.substring(start, start + 2)
      }
      return c.toString
    }
    if (c == '!') {
      var i = start + 1
      while (i < line.length && line(i).isDigit) i += 1
      return line.substring(start, i)
    }
    if (c == '=' || c == '-') {
      return c.toString
    }
    val sb = new StringBuilder
    var i = start
    while (i < line.length && !line(i).isWhitespace && !"(){}[],:;@\\*<>\"".contains(line(i))) {
      if (i + 1 < line.length) {
        val pair = line.substring(i, i + 2)
        if (pair == "->" || pair == "/\\" || pair == "\\/") {
          if (i == start) return pair else return sb.toString
        }
      }
      if (line(i) == '.' && i != start) return sb.toString
      if (line(i) == '=' && i != start) return sb.toString
      if (line(i) == '-' && i != start) return sb.toString
      sb += line(i)
      i += 1
    }
    val result = sb.toString
    if (result == "split" && i < line.length && line(i) == '@') {
      return "split@"
    }
    result
  }

  /*
   * BNFC layout algorithm:
   *   After a layout keyword, the next token's column becomes the block column.
   *   Tokens at that column get ; inserted before them.
   *   Tokens at a lesser column close the block with }.
   *   Layout stop keywords (e.g. "in") also close the current block.
   *   Explicit braces { } override layout for a block (tracked as column 0).
   */
  def insertLayout(tokens: List[PosToken]): List[String] = {
    val result = scala.collection.mutable.ListBuffer[String]()
    var layoutStack: List[Int] = Nil
    var expectLayout = false
    var i = 0

    while (i < tokens.length) {
      val tok = tokens(i)

      if (expectLayout) {
        expectLayout = false
        if (tok.text == "{") {
          result += tok.text
          layoutStack = 0 :: layoutStack
          i += 1
        } else {
          val blockCol = tok.col
          layoutStack = blockCol :: layoutStack
          result += "{"
          result += tok.text
          if (layoutKeywords.contains(tok.text)) expectLayout = true
          i += 1
        }
      } else {
        layoutStack match {
          case blockCol :: rest if blockCol > 0 =>
            if (layoutStopKeywords.contains(tok.text)) {
              result += "}"
              val (extraClose, remaining) = rest.span {
                case col if col > 0 => tok.col < col
                case _              => false
              }
              extraClose.foreach(_ => result += "}")
              layoutStack = remaining
              result += tok.text
              i += 1
            } else if (tok.col < blockCol) {
              result += "}"
              layoutStack = rest
            } else if (tok.col == blockCol && i > 0) {
              result += ";"
              result += tok.text
              if (layoutKeywords.contains(tok.text)) expectLayout = true
              i += 1
            } else if (tok.col < blockCol) {
              result += "}"
              layoutStack = rest
            } else {
              result += tok.text
              if (layoutKeywords.contains(tok.text)) expectLayout = true
              i += 1
            }
          case _ =>
            if (layoutStack.nonEmpty && layoutStack.head == 0 && tok.text == "}") {
              result += tok.text
              layoutStack = layoutStack.tail
              i += 1
            } else {
              result += tok.text
              if (layoutKeywords.contains(tok.text)) expectLayout = true
              i += 1
            }
        }
      }
    }

    while (layoutStack.nonEmpty) {
      if (layoutStack.head > 0) result += "}"
      layoutStack = layoutStack.tail
    }

    result.toList
  }

  def preprocess(source: String): List[String] = insertLayout(tokenize(source))
}
