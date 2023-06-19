object Main {
  def main(args: Array[String]): Unit = {
    var robot = Robot(Bearing.North, (7, 3))
    robot = robot.simulate("RAALAL")
    println(robot.coordinates) // (9, 4)
    println(robot.bearing) // west
  }
}

// scalac Robot.scala Main.scala && scala Main
