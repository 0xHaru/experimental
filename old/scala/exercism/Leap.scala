object Leap {
  def leapYear(year: Int) : Boolean = {
    val divisibleBy: Int => Boolean = year % _ == 0
    divisibleBy(400) || (divisibleBy(4) && !divisibleBy(100))
  }

  def main(args: Array[String]): Unit = {
    println(leapYear(2023)) // false
    println(leapYear(2024)) // true
  }
}

// scalac Leap.scala && scala Leap
