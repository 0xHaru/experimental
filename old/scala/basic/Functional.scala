object Functional {
  def isPalindrome(str: String): Boolean = {
    val letters = str.filter(ch => ch.isLetter).toLowerCase()
    return letters == letters.reverse
  }

  def isAnAnagram(str: String, dict: List[String]): Boolean = {
    val sortedDict = dict.map(str => str.sorted)
    return sortedDict.contains(str.sorted)
  }

  def factors(n: Int, fact: Int): List[Int] = {
    if(n == 1)
      return List()

    if(n % fact == 0)
      return fact :: factors(n / fact, fact)

    return factors(n, fact + 1)
  }

  def factors(n: Int): List[Int] = {
    return factors(n, 2)
  }

  def isProper(n: Int): Boolean = {
    val divisors = for (x <- 1 to (n / 2) if n % x == 0) yield x
    return divisors.foldLeft(0)((x, y) => x + y) == n
  }

  def main(args: Array[String]): Unit = {
    println(isPalindrome("detartrated"))        // true
    println(isPalindrome("Do geese see God?"))  // true
    println(isPalindrome("Rise to vote, sir.")) // true
    println(isPalindrome("Not a palindrome!"))  // false

    println()

    println(isAnAnagram("restful", List("functional", "programming", "fluster"))) // true
    println(isAnAnagram("restful", List("functional", "programming", "cluster"))) // false

    println()

    println(factors(60)) // List(2, 2, 3, 5)

    println()

    println(isProper(6)) // true
  }
}

// scalac Functional.scala && scala Functional
