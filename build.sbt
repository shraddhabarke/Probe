name := "probe"

version := "0.1"

scalaVersion := "3.2.2"

// https://mvnrepository.com/artifact/jline/jline
libraryDependencies += "jline" % "jline" % "2.14.6"

// https://mvnrepository.com/artifact/org.antlr/antlr4-runtime
libraryDependencies += "org.antlr" % "antlr4-runtime" % "4.7.2"

// https://mvnrepository.com/artifact/org.apache.commons/commons-lang3
libraryDependencies += "org.apache.commons" % "commons-lang3" % "3.9"

// https://mvnrepository.com/artifact/commons-io/commons-io
libraryDependencies += "commons-io" % "commons-io" % "2.6"

// https://mvnrepository.com/artifact/junit/junit
libraryDependencies += "junit" % "junit" % "4.13-rc-1" % Test

// https://mvnrepository.com/artifact/org.scalatest/scalatest
libraryDependencies += "org.scalatest" %% "scalatest" % "3.2.10" % Test

// https://mvnrepository.com/artifact/org.scalatestplus/scalatestplus-junit
libraryDependencies += "org.scalatestplus" %% "junit-4-13" % "3.2.15.0" % "test"

libraryDependencies += "junit" % "junit" % "4.12" % "test"

libraryDependencies += "org.scalatest" %% "scalatest" % "3.0.0" % "test"

libraryDependencies += "io.spray" %% "spray-json" % "1.3.6"

// https://mvnrepository.com/artifact/commons-cli/commons-cli
libraryDependencies += "commons-cli" % "commons-cli" % "1.4"

//mainClass in (assembly) := Some("pcShell.ShellMain")
Project.inConfig(Test)(baseAssemblySettings)
Test / assembly / assemblyJarName := s"${name.value}-full.jar"

javaOptions += "-Xmx10G"
//Anlr command line:
//java -jar antlr-4.7.2-complete.jar -package "sygus" -visitor SyGuS.g4