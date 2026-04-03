val scala3Version = "3.8.3"

lazy val root = project
  .in(file("."))
  .settings(
    name         := "cubicaltt-scala",
    version      := "0.1.0-SNAPSHOT",
    scalaVersion := scala3Version,

    libraryDependencies ++= Seq(
      "org.scala-lang.modules" %% "scala-parser-combinators" % "2.4.0",
      "org.scalatest" %% "scalatest" % "3.2.20" % Test
    ),

    scalacOptions ++= Seq(
      "-deprecation",
      "-feature",
      "-unchecked"
    ),

    // Main entry point
    Compile / mainClass := Some("cubical.Main"),

    // Exclude slow tests by default; run with:
    //  sbt 'set Test / testOptions := Seq()' "testOnly * -- -n Slow"
    Test / testOptions += Tests.Argument(TestFrameworks.ScalaTest, "-l", "Slow")
  )
