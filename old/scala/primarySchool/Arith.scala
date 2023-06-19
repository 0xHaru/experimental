import java.io.FileReader
import scala.util.parsing.combinator.JavaTokenParsers

class ArithParser extends JavaTokenParsers {
  def operator: Parser[String] = "+" | "-"

  def operand: Parser[Int] =
    operator ~ wholeNumber ^^ {
      case "+" ~ num => num.toInt
      case "-" ~ num => -(num.toInt)
    }

  def result: Parser[Int] =
    "=" ~> "-+".r ~> opt("-") ~ wholeNumber ^^ {
      case None ~ num => num.toInt
      case Some(_) ~ num => -(num.toInt)
    }

  def expr: Parser[(List[Int], Int)] =
    wholeNumber ~ rep1(operand) ~ result ^^ {
      case firstNum ~ numLst ~ res => (firstNum.toInt +: numLst, res)
    }
}

class ArithEval {
  def eval(expr: List[Int], res: Int): Boolean =
     expr.foldLeft(0)((acc, x) => acc + x) == res
}

object Main {
  def main(args: Array[String]) = {
    val p = new ArithParser()
    val e = new ArithEval()

    args.foreach { filename =>
      val reader = new FileReader(filename)
      p.parseAll(p.expr, reader) match {
        case p.Success((expr, res), _) => println(e.eval(expr, res))
        case x => println(x.toString)
      }
    }
  }
}
