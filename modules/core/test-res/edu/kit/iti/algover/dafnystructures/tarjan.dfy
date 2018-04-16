class C
{
   method m1()
   {
      m1();
      m2();
   }

   method m2()
   {
      m2();
      m3();
      m4();
   }

   method m3()
   {
      m2();
   }

   method m4()
   {

   }
}

method x1()
{
   x2();
   x4();
}

method x2()
{
   if 2 > 4
   {
     x2();
   }
   x3();
   x4();
}

method x3()
{
   x4();
   while 2 > 0
   {
      x1();
   }
}

method x4()
{
}