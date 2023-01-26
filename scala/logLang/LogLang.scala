import java.nio.file.Files;
import java.nio.file.Paths;
import scala.util.parsing.combinator.JavaTokenParsers
import java.io.FileReader
import scala.io.Source;
import scala.util.Try

class LogLangParser extends JavaTokenParsers {
  // Operation
  sealed trait Op {
    def exec: Boolean
  }

  case class Task(name: String, oplst: List[Op]) extends Op {
    override def exec: Boolean = {
      println(s"Task $name")

      oplst.foldLeft(1) {
          case (acc, op) => {
              val result = op.exec
              println(s"  [op$acc] $result")
              acc + 1
          }
      }

      return true
    }
  }

  case class Remove(fname: String) extends Op {
    override def exec: Boolean = {
      Try(
        Files.delete(Paths.get(fname))
      ).isSuccess
    }
  }

  case class Rename(fname: String, newFname: String) extends Op {
    override def exec: Boolean = {
      Try(
        Files.move(Paths.get(fname), Paths.get(newFname))
      ).isSuccess
    }
  }

  case class Merge(fname1: String, fname2: String, newFname: String) extends Op {
    override def exec: Boolean = {
      Try({
        val f1 = Source.fromFile(fname1)
        val f2 = Source.fromFile(fname2)
        val data = f1.getLines.mkString("\n") + f2.getLines.mkString("\n")
        f1.close
        f2.close
        Files.write(Paths.get(newFname), data.getBytes)
      }).isSuccess
    }
  }

  case class Backup(fname: String, newFname: String) extends Op {
    override def exec: Boolean = {
      Try(
        Files.copy(Paths.get(fname), Paths.get(newFname))
      ).isSuccess
    }
  }

  def tname: Parser[String] = ident // """[a-zA-Z][a-zA-Z0-9]*""".r

  // Remove quotation marks
  def fname: Parser[String] = stringLiteral ^^ { str => str.substring(1, str.length - 1) }

  def backup: Parser[Backup] =
    "backup" ~> fname ~ fname ^^ { case fname ~ newFname => Backup(fname, newFname) }

  def merge: Parser[Merge] =
    "merge" ~> fname ~ fname ~ fname ^^ {
      case fname1 ~ fname2 ~ newFname => Merge(fname1, fname2, newFname)
    }

  def rename: Parser[Rename] =
    "rename" ~> fname ~ fname ^^ { case fname ~ newFname => Rename(fname, newFname) }

  def remove: Parser[Remove] = "remove" ~> fname ^^ { case fname => Remove(fname) }

  def op: Parser[Op] = remove | rename | merge | backup

  def oplst: Parser[List[Op]] = rep(op) // repsep(op, "\n") => WHITESPACE IS SKIPPED BY DEFAULT YOU CAN'T USE THIS!!!

  def task: Parser[Task] =
    "task" ~> tname ~ ("{" ~> oplst <~ "}") ^^ {
      case tname ~ oplst => Task(tname, oplst)
    }

  def prog: Parser[List[Task]] = rep(task)
}


object Main extends LogLangParser {
  def main(args: Array[String]) : Unit = {
    val reader = new FileReader(args(0))

    parseAll(prog, reader) match {
        case Success(lst: List[Task], _) => {
          println(lst)
          println()
          lst.foreach(task => task.exec)
        }
        case Failure(msg, _) => println("FAILURE: " + msg)
        case Error(msg, _)  => println("ERROR: " + msg)
      }
    }
}
