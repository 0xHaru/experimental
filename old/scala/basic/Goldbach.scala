import scala.math.sqrt

object Goldbach {
  def isPrime(n: Int): Boolean = {
    if (n <= 1)
      return false

    if(n == 2 || n == 3)
      return true

    return !(2 to sqrt(n).toInt).exists(x => n % x == 0)
  }

  def goldbach(n: Int): (Int, Int) = {
    def aux(x: Int): (Int, Int) = {
      if (isPrime(x) && isPrime(n - x))
        return (x, n - x)

      return aux(x + 1)
    }

    return aux(1)
  }

  def goldbachList(n: Int, m: Int): List[(Int, Int)] = {
    return for (x <- List.range(n, m + 1); if x % 2 == 0) yield goldbach(x);
  }


  def main(args: Array[String]): Unit = {
    println(isPrime(97)) // true
    println(isPrime(98)) // false

    println()

    println(goldbach(10)) // (7, 3)
    println(goldbach(12)) // (5, 7)
    println(goldbach(14)) // (3, 11)

    println()

    println(goldbachList(10, 14)) // List((3,7), (5,7), (3,11))
  }
}

// scalac Goldbach.scala && scala Goldbach
