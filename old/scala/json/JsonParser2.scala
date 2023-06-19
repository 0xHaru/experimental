import java.io.FileReader
import scala.util.parsing.combinator._

class JsonParser2 extends JavaTokenParsers {
  def obj: Parser[Map[String, Any]] =
    "{" ~> repsep(member, ",") <~ "}" ^^ { lst => Map() ++ lst }

  def arr: Parser[List[Any]] =
    "[" ~> repsep(value, ",") <~ "]" ^^ { lst => lst }

  def member: Parser[(String, Any)] =
    stringLiteral ~ ":" ~ value ^^ { case name ~ _ ~ value => (name, value) }

  def value: Parser[Any] = (
    obj
  | arr
  | stringLiteral
  | floatingPointNumber ^^ { n => n.toDouble }
  | "null"  ^^ (x => null)
  | "true"  ^^ (x => true)
  | "false" ^^ (x => false)
  )
}

object JsonParser2 {
  def main(args: Array[String]) = {
    val parser = new JsonParser2()
    val reader = new FileReader("test.json")
    println(parser.parseAll(parser.value, reader))
  }
}
