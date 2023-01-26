object Bob {
  def response(statement: String): String = {
    // use () because trim has side effects
    val input = statement.trim()

    // don't use (), because isEmpty has no side effects
    if (input.isEmpty)
      return "Fine. Be that way!"

    val isUppercase = input.exists(_.isLetter) && input.toUpperCase() == input

    (input.endsWith("?"), isUppercase) match {
      case (true, true) => "Calm down, I know what I'm doing!"
      case (_, true)    => "Whoa, chill out!"
      case (true, _)    => "Sure."
      case _            => "Whatever."
    }
  }

  def main(args: Array[String]): Unit = {
    println(response("WHAT'S YOUR NAME?")) // Calm down, I know what I'm doing!
    println(response("MOW THE LAWN")) // Whoa, chill out!
    println(response("Could you pass me that glass?")) // Sure.
    println(response("My name is Steve")) // Whatever.
  }
}

// scalac Bob.scala && scala Bob
