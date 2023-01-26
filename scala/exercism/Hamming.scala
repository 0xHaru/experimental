object Hamming {
  def distance(a: String, b: String): Option[Int] = {
    if(a.length != b.length)
      None
    else
      Some(a.zip(b).count(t => t._1 != t._2))
  }

  def extract(opt: Option[Int]): Int = {
    opt match {
      case Some(int) => int
      case None => -1
    }
  }

  def main(args: Array[String]): Unit = {
    val d1 = distance("GAGCCTACTAACGGGAT", "CATCGTAATGACGGCCT")
    val d2 = distance("GAGCCTACTAACGGGAT", "GAGCCTACTAACGGGAT")
    println(extract(d1)) // 7
    println(extract(d2)) // 0
  }
}

// scalac Hamming.scala && scala Hamming
