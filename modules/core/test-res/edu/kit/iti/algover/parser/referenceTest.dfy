
/* Test case for name resolution,
 * all entities are of type int.
 *
 * The names are prefixed by their type.
 * p_ = paramters
 * l_ = local variables
 * m_ = method
 * f_ = function
 * fl_ = field
 * vx = exists var
 * va = forall var
 * vl = let var
 */

method m_topmethod()
{
  var l_x: int;
  l_x := 1;
  m_topmethod();
}

function f_global(p_param: int) : int 
{
   p_param + f_global(0)
}

class C {

   var fl_var : int;
   var l_conflict : int;
   var p_conflict : int;

   function f_class(p_param: int) : int {
      p_param * fl_var
   }

   method m_method(p_param: int)
     requires f_class(p_param) == p_param
     requires label req_label: p_param > 0 && fl_var < 0
     ensures label ens_label: p_param < 0 && fl_var > 0
     ensures forall va_x: int :: va_x > 0 ==> f_global(va_x) > 0
     ensures let vl_1, vl_2 := 11, 22 :: vl_1 < vl_2
   {
      var l_top: int;

      l_top := 5;
      l_top := 6;

      var l_middle: int;

      label cond_label: if l_top > 0 {
         var l_diff1: int;
         l_diff1 := l_middle;
         m_method(l_diff1);
      } else {
         var l_diff2: int;
         l_diff2 := l_top + 1;
         m_method(l_diff2);
      }

      while *
        invariant label inv_label: p_param > fl_var
        invariant (exists vx_y: int :: vx_y == 0)
        decreases l_top - p_param
      {
         var l_local: int;
         l_local := l_middle;
      }

      m_topmethod();
      m_method(f_global(f_class(l_top)));

      fl_var := 55;
      this.fl_var := 55;
   }

   method returnsValue(p_param : array<int>) returns (ret_r : int)
     ensures ret_r == p_param[0] + 1
   {
     ret_r := p_param[0] + 1;
   }

   method conflictVarField()
   {
     var l_conflict : int;
     // This is allowed!
     l_conflict := 2;
   }

   method conflictParamField(p_conflict: int)
   {
     // This is allowed!
     var x := p_conflict + 2;
   }

}

method varDecls() returns (ret_r : int)
 {
     var l_i : int;
     var l_x1, l_x2 : int;
     var l_y : int := 42;
     var l_v := 44;

     ret_r := l_i+l_x1+l_x2+l_y+l_v;
 }

method double_quantifiers()
  ensures forall va_i, va_j : int :: va_i > va_j
  ensures exists vx_i, vx_j : int :: vx_i > vx_j
{}

// bug report #44
method getSum (p_a: int, p_b: int) returns (ret_m: int)
    requires p_a > 0 && p_b > 0
    ensures ret_m > 0
{
    var l_sum := p_a + p_b;
    ret_m := l_sum;
}
