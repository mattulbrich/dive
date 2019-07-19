# Dafny Interactive Verification Environment (DIVE)

A new interaction concept for the interactive verification of
[Dafny](https://github.com/microsoft/dafny) programs.

![DIVE logo][divelogo]

*The logo design is artistically inspired by the Dafny logo.*

----

[![Build Status](http://hudson.se.informatik.tu-darmstadt.de/buildStatus/icon?job=DIVE-master)](http://hudson.se.informatik.tu-darmstadt.de/job/DIVE-master)

DIVE is developed at the [Karlsruhe Institute of Technology](https://formal.kit.edu/).

We develop this interactive program verification environment to
promote and experiment with new ways of interaction in program
verification.  It is a graphical proof front end for programs written
and specified in Dafny and supports different types of user guidance
for proofs:

1. *Autoactive* annotations within the source code can be used to
   guide the automated prover. (That's how Dafny itself works)
2. Textual *proof scripts* can be written to discharge proof
   obligations in a programmatic fashion.
3. Interactive *point-and-click* directives can be used to apply a
   sequence proof steps to an open proof goal (direct interaction).

DIVE is open source (GPL) and written in Java.



## Requirements

* Java (OpenJDK or Oracle JDK, at least version 11) must be installed.
* Boogie must be installed and in path (and then, Z3 is also available)
For Ubuntu (version 18.04 or higher) run `sudo apt-get install boogie`. In other cases refer to
[Boogie Github](https://github.com/boogie-org/boogie)

## Run it

After cloning the repository, invoke `./gradlew run` (on Linux/iOS) or
`gradle.bat run` (on Windows).

An example is included in DIVE and accessible in the WelcomePane using the button "Load example".

## Boogie

will be called as `boogie`. Hence it must be in the path.

If not, you can set the path to your boogie executable using an
environment variable.

[divelogo]: doc/logo.png
