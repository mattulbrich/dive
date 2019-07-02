// These comments must be kept
/*
 * Single Line and multiline
 */
// ---- Automatically generated settings ----
//> settings {
//>    "Dafny Timeout" = "100",
//>    "Default Script" = "boogie;"
//> }
     include "lib1.dfy"
     include "/absolute/lib2.dfy"
     include "with spaces lib.dfy"
//> subsume "file1.dfy"
//> subsume "/absolute/file2.dfy"
//> subsume "with spaces.dfy"
// ---- End of settings ----

class C {

 // These lines must not be touched
 method m()
 {
   var f : int;
 }

}