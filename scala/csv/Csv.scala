import scala.util.parsing.combinator.RegexParsers
import java.io.FileReader

class CsvParser extends RegexParsers {
  // Whitespace is meaningful in CSV files
  override val skipWhitespace = false

  // [^,\n] match everything that isn't (^) a comma (,) or a newline (\n)
  def field: Parser[String] = "[^,\n]*".r

  def record: Parser[List[String]] = repsep(field, ",")

  def csvfile: Parser[List[List[String]]] = repsep(record, "\n") ^^ { csv => csv.dropRight(1) }
}

class CsvPPrinter(csv: List[List[String]]) {
  val header = csv(0)
  val rows = csv
  val cols = csv.transpose // Get the columns by transposing the n-dimensional list

  def getColsWidth: List[Int] = {
    // Get the longest words in each column and extract their length
    cols.map(col => col.maxBy(_.length).length)
  }

  def getTableWidth: Int = {
    val tableWidth = getColsWidth.foldLeft(0)((acc, x) => acc + x)
    // Let's take into account the  vertical bars (|) and spaces
    tableWidth + (header.length + 1) + (header.length * 2)
  }

  def getTableHeight: Int = csv.length + 3 // 3 dashed horizontal dividers (-)

  def repeat(str: String, n: Int): String = if (n <= 1) str else str ++ repeat(str, n - 1)

  def pprint: Unit = {
    // Print the first dashed divider
    println(repeat("-", getTableWidth))

    // Print the rest of the rows
    print("| ")

    // Associate to each element of a row the length of the longest element in its column
    header.zip(getColsWidth).foreach { case (elem, size) =>
      print(elem)
      print(repeat(" ", size - elem.length + 1)) // Print the padding
      print("| ")
    }

    println()

    // Print the second dashed divider
    println(repeat("-", getTableWidth))

    // Print the rest of the rows
    rows.drop(1).foreach { row =>
      print("| ")

      // Associate to each element of a row the length of the longest element in its column
      row.zip(getColsWidth).foreach { case (elem, size) =>
        print(elem)
        print(repeat(" ", size - elem.length + 1)) // Print the padding
        print("| ")
      }

      println()
    }

     // Print the last dashed divider
    println(repeat("-", getTableWidth))
  }
}

object Main extends CsvParser {
    def main(args: Array[String]) : Unit = {
      val reader = new FileReader("test.csv")

      parseAll(csvfile, reader) match {
        case Success(csv, _) => {
          // println(csv)
          val pprinter = new CsvPPrinter(csv)
          pprinter.pprint
        }
        case Failure(msg, _) => println("FAILURE: " + msg)
        case Error(msg, _) => println("ERROR: " + msg)
      }
    }
}

