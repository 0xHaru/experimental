object Etl {
  def transform1(values: Map[Int, Seq[String]]): Map[String, Int] = {
    for {
      (value, letters) <- values
      letter <- letters
    } yield (letter.toLowerCase(), value)
  }

  def transform2(values: Map[Int, Seq[String]]): Map[String, Int] = {
    values.flatMap { case (value, letters) =>
      letters.map(letter => (letter.toLowerCase(), value))
    }
  }

  def main(args: Array[String]): Unit = {
    val values = Map(
      1  -> Seq("A", "E", "I", "O", "U", "L", "N", "R", "S", "T"),
      2  -> Seq("D", "G"),
      3  -> Seq("B", "C", "M", "P"),
      4  -> Seq("F", "H", "V", "W", "Y"),
      5  -> Seq("K"),
      8  -> Seq("J", "X"),
      10 -> Seq("Q", "Z")
    )

    println(transform1(values))
    println(transform2(values))
  }
}

// scalac Etl.scala && scala Etl
