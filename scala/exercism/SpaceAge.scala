object SpaceAge {
  private val earthOrbitalPeriod = 31557600.0

  private val ratio = Map(
    "mercury" -> 0.2408467,
    "venus"   -> 0.61519726,
    "earth"   -> 1.0,
    "mars"    -> 1.8808158,
    "jupiter" -> 11.862615,
    "saturn"  -> 29.447498,
    "uranus"  -> 84.016846,
    "neptune" -> 164.79132
  )

  private val trunc = (input: Double) => "%.02f".format(input).toDouble

  def spaceAge(age: Int): Unit = {
    ratio.foreach { case(planet, ratio) =>
      val planetAge = trunc((age / earthOrbitalPeriod) / ratio)
      println(s"$planet : $planetAge")
    }
  }

  def main(args: Array[String]): Unit = {
    spaceAge(1000000000)
  }
}

// scalac SpaceAge.scala && scala SpaceAge
