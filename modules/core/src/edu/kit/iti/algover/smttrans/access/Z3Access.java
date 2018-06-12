package edu.kit.iti.algover.smttrans.access;

import java.util.HashMap;

import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;
import com.microsoft.z3.Model;
import com.microsoft.z3.Solver;
import com.microsoft.z3.Status;
import com.microsoft.z3.Version;
import com.microsoft.z3.Z3Exception;

public class Z3Access extends AccessStrategy{

    public String debugsmt = "(declare-sort X)(declare-sort Heap)(declare-sort Field 2)(declare-fun fieldstoreXInt (Heap X (Field X Int) Int) Heap)(declare-fun fieldselectXInt (Heap X (Field X Int)) Int)(declare-const heap Heap)(declare-const X.y (Field X Int))(declare-const nullX X)(declare-const o X)(assert (not (= o nullX)))(assert (= heap (fieldstoreXInt heap o X.y 8)))(assert (> (fieldselectXInt heap o X.y) 5))";
	@Override
	public SolverResponse accessSolver() {
	    SolverResponse sr = new SolverResponse();
	 
        Context ctx = new Context();
        BoolExpr f = ctx.parseSMTLIB2String(debugsmt,null,null,null,null);
        Solver s = ctx.mkSolver();
        
      
           
 
         
           

       
        if(s.check() == Status.SATISFIABLE) {
            Model model = s.getModel();
            System.out.println("SAT");
            System.out.println(model.getNumConsts());
            System.out.println(model.getNumFuncs());
            System.out.println(model.getNumSorts());
            System.out.println(model.getConstDecls().toString());
            System.out.println(model.getSorts().toString());
            System.out.println(model);

            
        } else {
            System.out.println("UNSAT");
        }
        
        return sr;
       
	}

}
