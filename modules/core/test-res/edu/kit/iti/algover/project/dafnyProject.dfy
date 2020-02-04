
// Testing parsing/setting of these entities on top

//> include "sub/i1.dfy"
include "sub/i2.dfy"

//> subsume "sub/s1.dfy"
subsume "sub/s2.dfy"

settings {
   "Default Script" = "test"
}