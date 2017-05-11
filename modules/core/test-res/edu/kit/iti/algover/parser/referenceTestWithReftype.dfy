
/* Test case for name resolution,
 * all entities are of type C_Class.
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
  var l_x: C_Class;
  l_x := null;
  m_topmethod();
}

function f_global(p_param: C_Class) : C_Class 
{
   p_param.f_class(p_param.fl_var)
}

class C_Class {

   var fl_var : C_Class;

   function f_class(p_param: C_Class) : C_Class {
      p_param.fl_var
   }

   method m_method(p_param: C_Class) returns (p_return: C_Class)
     requires p_param != fl_var
     ensures p_param != fl_var
   {
      var l_top: C_Class;

      l_top := null;
      l_top := fl_var;

      var l_middle: C_Class;

      if l_top == null
      {
         var l_diff1: C_Class;
         l_diff1 := l_middle;
         m_method(l_diff1);
      } else {
         var l_diff2: C_Class;
         l_diff2 := l_top.fl_var;
         m_method(l_diff2);
      }

      while *
        invariant p_param == fl_var
        invariant (exists vx_y: C_Class :: vx_y == fl_var)
        decreases 2
      {
         var l_local: C_Class;
         l_local := l_middle;
      }

      m_topmethod();
      m_method(f_global(f_class(l_top)));
   }
}
