# Dafny Interactive Verification Envireonment (DIVE)
A new interaction concept for the interactive verification of Dafny programs.

----

[![Build Status](http://hudson.se.informatik.tu-darmstadt.de/buildStatus/icon?job=AlgoVer)](http://hudson.se.informatik.tu-darmstadt.de/job/AlgoVer/)

To experiment with new ways of interactive program verification, we develop this user interface.
It is a graphical proof front end for programs written and specified in Dafny.

The tool is written in Java.

## Requirements

* Java (oracle JDK, at least 8) must be installed.
* ANT must be installed
* Z3 must be installed
* boogie must be installed
## Run it

After downloading run `ant jar` in the project  directory to build the tools.
Then call `java -jar algover.jar` to run it.

An example can be found in the folder ListExample.

