class Kwic {
  private val irrelevantWords = List("about", "and", "but", "for", "of", "over", "the", "to")

  private def explodeTitle(title: String, index: Int): IndexedSeq[String] = {
    val words = title.split(" ")

    return (0 to words.size - 1)
    .filterNot(i => irrelevantWords.contains(words(i).toLowerCase()))
    .map(i => words.splitAt(i))
    .map({case (l, r) => (l.mkString(" "), r.mkString(" "))})
    .map({case (l, r) => f"${index + 1}%4d ${l.substring(Math.max(l.length, 33) - 33)}%33s ${r.substring(0, Math.min(r.length, 40))}%-40s"})
  }

  def kwic(titles: List[String]) = {
    titles
    .zipWithIndex
    .map({case (title, i) => explodeTitle(title, i)})
    .flatten
    .toList
    .sortWith((t1, t2) => t1.substring(39) < t2.substring(39))
  }
}

object Kwic {
  def main(args: Array[String]) = {
    val filename = "kwic.txt"
    val kwic = new Kwic()
    val titles = scala.io.Source.fromFile(filename).getLines().toList
    kwic.kwic(titles).foreach(x => println(x))
  }
}

// scalac Kwic.scala && scala Kwic
