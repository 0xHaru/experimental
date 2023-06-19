object Comprehensions {
  def squared_numbers(lst: List[Any]): List[Any] = {
    lst.collect(elem =>
      elem match {
        case i: Int       => i * i
        case d: Double    => d * d
        case l: List[Any] => squared_numbers(l)
        case p: Product   => squared_numbers(p.productIterator.toList)
      }
    )
  }

  def intersect(lst1: List[Any], lst2: List[Any]): List[Any] = {
    return for(e1 <- lst1; e2 <- lst2; if e1 == e2) yield e1
  }

  def symmetricDifference(lst1: List[Any], lst2: List[Any]): List[Any] = {
    return (for (e1 <- lst1; if !lst2.contains(e1)) yield e1) ++
           (for (e2 <- lst2; if !lst1.contains(e2)) yield e2);
  }

  def symmetricDifference2(lst1: List[Any], lst2: List[Any]): List[Any] = {
    return lst1.diff(lst2) ++ lst2.diff(lst1)
  }


  def main(args: Array[String]): Unit = {
    // List(1, 10000, 9.8596, List(100), List(25, 49))
    println(squared_numbers(1 :: "hello" :: 100 :: 3.14 :: ("a" :: 10 :: Nil) :: "c" :: (5, 7, "a") :: Nil))

    println()

    println(intersect(List(1,2,3,4,5), List(4,5,6,7,8))) // List(4,5)

    println()

    println(symmetricDifference(List(1,2,3,4,5), List(4,5,6,7,8))) // List(1, 2, 3, 6, 7, 8)
    println(symmetricDifference2(List(1,2,3,4,5), List(4,5,6,7,8))) // List(1, 2, 3, 6, 7, 8)
  }
}

// scalac Comprehensions.scala && scala Comprehensions
