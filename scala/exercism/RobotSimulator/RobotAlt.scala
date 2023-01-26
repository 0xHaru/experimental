object Bearing extends Enumeration {
  val North = Value("north")
  val South = Value("south")
  val East = Value("east")
  val West = Value("west")
}

case class Robot(bearing: Bearing.Value, coordinates: (Int, Int)) {
  def turnLeft(): Robot = {
    val newBearing = bearing match {
      case Bearing.North => Bearing.West
      case Bearing.East  => Bearing.North
      case Bearing.South => Bearing.East
      case Bearing.West  => Bearing.South
    }

    this.copy(bearing = newBearing, coordinates = coordinates)
  }

  def turnRight(): Robot = {
    val newBearing = bearing match {
      case Bearing.North => Bearing.East
      case Bearing.East  => Bearing.South
      case Bearing.South => Bearing.West
      case Bearing.West  => Bearing.North
    }

    this.copy(bearing = newBearing, coordinates = coordinates)
  }

  def advance(): Robot = {
    val newCoords = bearing match {
      case Bearing.North => (coordinates._1, coordinates._2 + 1)
      case Bearing.South => (coordinates._1, coordinates._2 - 1)
      case Bearing.East  => (coordinates._1 + 1, coordinates._2)
      case Bearing.West  => (coordinates._1 - 1, coordinates._2)
    }

    this.copy(bearing = bearing, coordinates = newCoords)
  }

  def simulate(instructions: String): Robot = {
    instructions.foldLeft(this)((robot, char) =>
      char.toString match {
        case "A" => robot.advance()
        case "L" => robot.turnLeft()
        case "R" => robot.turnRight()
      }
    )
  }
}

