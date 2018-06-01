package edu.kit.iti.algover.smttrans.access;

import java.util.HashMap;


public class SolverAccess {
	
	public static SolverResponse evaluate(String smt) {

		SolverResponse sr = new SolverResponse();
//		System.out.print("Z3 Full Version String: ");
//		System.out.println(Version.getFullVersion());
//        HashMap<String, String> cfg = new HashMap<String, String>();
//        cfg.put("model", "true");
//        Context ctx = new Context(cfg);
//
//        BoolExpr x = ctx.mkBoolConst("x");
//        BoolExpr y = ctx.mkBoolConst("y");
//        BoolExpr x_xor_y = ctx.mkXor(x, y);
//        Solver s = ctx.mkSolver();
//        s.add(x_xor_y);
//        if(s.check() == Status.SATISFIABLE) {
//            Model model = s.getModel();
//           //System.out.println("x = " + model.evaluate(x, false) + ", y = "
//            //        + model.evaluate(y, false));
////            System.out.println(model.getNumConsts());
////            System.out.println(model.getNumFuncs());
////            System.out.println(model.getNumSorts());
////            System.out.println(model.getConstDecls().toString());
////            System.out.println(model.getSorts().toString());
////            System.out.println(model);
////            System.out.println(model);
////              System.out.println(model);
//            
//        } else {
//        	System.out.println("UNSAT");
//        }
		
		return sr;
		
		
	}

}
