object Bearing extends Enumeration {
  val North = Value("north")
  val South = Value("south")
  val East = Value("east")
  val West = Value("west")
}

case class Robot(bearing: Bearing.Value, coordinates: (Int, Int)) {
  def turnLeft(): Robot = {
    bearing match {
      case Bearing.North => Robot(Bearing.West,  coordinates)
      case Bearing.East  => Robot(Bearing.North, coordinates)
      case Bearing.South => Robot(Bearing.East,  coordinates)
      case Bearing.West  => Robot(Bearing.South, coordinates)
    }
  }

  def turnRight(): Robot = {
    bearing match {
      case Bearing.North => Robot(Bearing.East,  coordinates)
      case Bearing.East  => Robot(Bearing.South, coordinates)
      case Bearing.South => Robot(Bearing.West,  coordinates)
      case Bearing.West  => Robot(Bearing.North, coordinates)
    }
  }

  def advance(): Robot = {
    val (x, y) = coordinates

    bearing match {
      case Bearing.North => Robot(bearing, (x, y + 1))
      case Bearing.South => Robot(bearing, (x, y - 1))
      case Bearing.East  => Robot(bearing, (x + 1, y))
      case Bearing.West  => Robot(bearing, (x - 1, y))
    }
  }

  def simulate(instructions: String): Robot = {
    // foldLeft (<identity-element>) ((a, b) => ...)
    //
    // Example:
    //   foldLeft(0)((a, b) => a + b)
    //
    // In this case the identity element is the object itself (this)
    instructions.foldLeft(this)((robot, char) =>
      char.toString match {
        case "A" => robot.advance()
        case "L" => robot.turnLeft()
        case "R" => robot.turnRight()
        case x   => sys.error("Invalid instruction: " + x)
      }
    )
  }
}

