# Dafny Interactive Verification Environment (DIVE)

[![Build Status](http://hudson.se.informatik.tu-darmstadt.de/buildStatus/icon?job=AlgoVer)](http://hudson.se.informatik.tu-darmstadt.de/job/AlgoVer/)
DIVE is a prototypical implementation of a new seamless interaction concept for the deductive program verification of Dafny programs.

The purpose is to experiment with new ways of user interaction in interactive program verification. 

DIVE is implemented in Java.

## Requirements to build the sources

* OpenJDK 11 must be installed.
* Gradle version 5.4.1 or higher

## Requirements to run DIVE

* Java 11 must be installed.
* OpenJFX 12 must be installed.
* boogie must be installed. For Ubuntu (version 18.04 or higher) run `sudo apt-get install boogie`. In other cases refer to
[Boogie Github](https://github.com/boogie-org/boogie)


## Run it

After downloading run `./gradlew shadowJar` in the project directory to build the tools.
Then call `java -jar DIVE.jar` to run it.
Alternatively run `./gradlew run` to run DIVE.

An example is included in DIVE and accessible in the WelcomePane using the button "Load example".

