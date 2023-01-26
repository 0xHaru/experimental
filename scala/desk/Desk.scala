import java.io.FileReader
import scala.util.parsing.combinator.JavaTokenParsers

class DeskLangParser extends JavaTokenParsers {
  // Mimicking algebraic data types
  sealed trait Expr {
    def eval: Int
  }

  case class Sum(left: Expr, right: Expr) extends Expr {
    override def eval: Int = left.eval + right.eval
  }

  case class Num(value: Int) extends Expr {
    override def eval: Int = value
  }

  case class Ident(value: String) extends Expr {
    // It's a closure
    override def eval: Int = env(Ident(value)).value
  }

  var env: Map[Ident, Num] = Map()

  // Pass the [lst] in reverse
  def listToAst(lst: List[Expr]): Expr = {
    lst match {
      case Nil => throw new Exception("Expr list can't be 'Nil'")
      case a :: Nil => a
      case a :: b :: Nil => Sum(b, a)
      case h :: t => Sum(listToAst(t), h)
    }
  }

  def integer: Parser[Num] = wholeNumber ^^ { n => Num(n.toInt) }

  def identifier: Parser[Ident] = """[a-zA-Z]+""".r ^^ { i => Ident(i) }

  def term: Parser[Expr] = identifier | integer

  def assign: Parser[Num] =
    identifier ~ "=" ~ integer ^^ { case id ~ _ ~ int => env += (id -> int); int }

  def decl: Parser[List[Num]] = repsep(assign, ",")

  def expr: Parser[Expr] = repsep(term, "+") ^^ { lst => listToAst(lst.reverse) }

  def prog: Parser[Expr] = "print" ~> expr <~ "where" <~ decl
}

object Main extends DeskLangParser {
    def main(args: Array[String]) : Unit = {
      args.foreach {
        filename => {
          val reader = new FileReader(filename)

          parseAll(prog, reader) match {
            case Success(ast: Expr, _) => println(ast); println(ast.eval)
            case Failure(msg, _) => println("FAILURE: " + msg)
            case Error(msg, _) => println("ERROR: " + msg)
          }

          println("---")
        }
      }

      // val input = "print x + y + z + 1 + x + -3 where x = 25, y = 1, z = -7"
      // parseAll(prog, input) match {
      //   case Success(ast: Expr,_) => println(ast); println(ast.eval)
      //   case Failure(msg,_) => println("FAILURE: " + msg)
      //   case Error(msg,_) => println("ERROR: " + msg)
      // }
    }
}
