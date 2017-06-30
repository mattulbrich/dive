
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

   function f_class(p_param: int) : int {
      p_param * fl_var
   }

   method m_method(p_param: int)
     requires label req_label: p_param > 0 && fl_var < 0
     ensures label ens_label: p_param < 0 && fl_var > 0
     ensures (forall va_x: int :: va_x > 0 ==> f_global(va_x) > 0)
   {
      var l_top: int;

      l_top := 5;
      l_top := 6;

      var l_middle: int;

      if l_top > 0 {
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
}
