import scala.collection.immutable.SortedMap

class School {
  type DB = Map[Int, Seq[String]]

  var db: DB = SortedMap.empty[Int, Seq[String]]

  def getDb(): DB = db

  def add(name: String, grade: Int): Unit = {
    db = db.updatedWith(grade) { opt => opt match {
      case None => Some(Seq(name))
      case Some(students) => Some(students.filter(_ != name) :+ name)
    }}
  }

  def getStudents(grade: Int): Seq[String] = db.getOrElse(grade, Seq.empty[String])

  def getSorted(): DB = db.map { case (k, v) => (k, v.sorted) }

  def main(args: Array[String]): Unit = {
    add("Foo",   1)
    add("Bar",   1)
    add("Alice", 2)
    add("Bob",   2)

    println(getDb().toString())
    println(getStudents(1).toString())
    println(getSorted().toString())
  }
}

// scalac GradeSchool.scala && scala GradeSchool
