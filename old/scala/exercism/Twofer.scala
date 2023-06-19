object Twofer {
  def twofer(name: String = "you"): String = {
    s"One for $name, one for me."
  }

  def main(args: Array[String]): Unit = {
    println(twofer()) // One for you, one for me.
    println(twofer("FooBar")) // One for FooBar, one for me.
  }
}

// scalac Twofer.scala && scala Twofer
