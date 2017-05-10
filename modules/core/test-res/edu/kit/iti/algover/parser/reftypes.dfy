class LinkedList {

   var next : LinkedList;
   var prev : LinkedList;
   var tail : seq<LinkedList>;

   var exotic : set<seq<LinkedList>>;

   method m(x : LinkedList, a : array<int>) returns (y : LinkedList)
     ensures 1 == 1
   {
   z.next.next := null;

 /*     var z : LinkedList;
      // "this" is optional
      z := next;
      next := z;

      // explicit "this"
      z := this.next;
      this.next := z;

      // explicit receiver
      z := z.next;
      x.next := z;

      z.next := this.prev;
      x.next.next := this.prev.prev;

      // lets look at arrays ...
      a[0] := a[1];

      y := z;*/
   }

}