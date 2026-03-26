val scala3Version = "3.4.2"

lazy val root = project
  .in(file("."))
  .settings(
    name         := "cubicaltt-scala",
    version      := "0.1.0-SNAPSHOT",
    scalaVersion := scala3Version,

    libraryDependencies ++= Seq(
      "org.scala-lang.modules" %% "scala-parser-combinators" % "2.3.0",
      "org.scalatest" %% "scalatest" % "3.2.18" % Test
    ),

    scalacOptions ++= Seq(
      "-deprecation",
      "-feature",
      "-unchecked"
    ),

    // Main entry point
    Compile / mainClass := Some("cubical.Main")
  )
