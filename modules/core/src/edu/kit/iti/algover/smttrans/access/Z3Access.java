package edu.kit.iti.algover.smttrans.access;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.OutputStream;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;

import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;
import com.microsoft.z3.FuncDecl;
import com.microsoft.z3.Model;
import com.microsoft.z3.Solver;
import com.microsoft.z3.Status;
import com.microsoft.z3.Version;
import com.microsoft.z3.Z3Exception;

import edu.kit.iti.algover.smt.SMTException;
import edu.kit.iti.algover.smt.SMTSolver.Result;
import edu.kit.iti.algover.term.Term;

public class Z3Access extends AccessStrategy{

    //public String debugsmt = "(declare-sort X)(declare-sort Heap)(declare-sort Field 2)(declare-fun fieldstoreXInt (Heap X (Field X Int) Int) Heap)(declare-fun fieldselectXInt (Heap X (Field X Int)) Int)(declare-const heap Heap)(declare-const X.y (Field X Int))(declare-const nullX X)(declare-const o X)(assert (not (= o nullX)))(assert (= heap (fieldstoreXInt heap o X.y 8)))(assert (> (fieldselectXInt heap o X.y) 5))";
	public String debugsmt = "\r\n" + 
	        "      (declare-sort Heap)\r\n" + 
	        "      (declare-sort ArrInt)\r\n" + 
	        "      (declare-const heap Heap)\r\n" + 
	        "      (declare-const null.1 ArrInt)\r\n" + 
	        "      (declare-const a.1 ArrInt)\r\n" + 
	        "      (declare-const max.1 Int)\r\n" + 
	        "      (declare-const i.1 Int)\r\n" + 
	        "      (declare-const k.1 Int)\r\n" + 
	        "      (declare-fun  arrselectInt (Heap ArrInt Int) Int)\r\n" + 
	        "      (declare-fun  arrstoreInt (Heap ArrInt Int Int) Heap)\r\n" + 
	        "      (declare-fun arrlenInt (ArrInt) Int)\r\n" + 
	        "      (assert\r\n" + 
	        "      (forall\r\n" + 
	        "      (\r\n" + 
	        "          (i Int)\r\n" + 
	        "          (h Heap)\r\n" + 
	        "          (a ArrInt)\r\n" + 
	        "          (v Int)\r\n" + 
	        "      )\r\n" + 
	        "      (!\r\n" + 
	        "          (= (arrselectInt (arrstoreInt h a i v) a i) v) :pattern((arrstoreInt h a i v))\r\n" + 
	        "      )))\r\n" + 
	        "     \r\n" + 
	        "      (assert (not (= a.1 null.1)))\r\n" + 
	        "      (assert (>= (arrlenInt a.1) 1))\r\n" + 
	        "      (assert (= max.1 (arrselectInt heap a.1 0)))\r\n" + 
	        "      (assert(= i.1 1))\r\n" + 
	        "      (assert(not(forall((k.1 Int))(=> (and (<= 0 k.1) (< k.1 i.1)) (<= (arrselectInt heap a.1 k.1) max.1)))))";
    @Override
	public SolverResponse accessSolver() {
	    SolverResponse sr = new SolverResponse();

	    
	    Process process;
	    try {
	    process = buildProcess();
        
            OutputStream out = process.getOutputStream();
            InputStream in = process.getInputStream();

            out.write(debugsmt.getBytes());
            out.write("(check-sat)".getBytes());
            out.write("(get-model)".getBytes());
            out.close();
            List<String> r = new ArrayList<>();
            BufferedReader br = new BufferedReader(new InputStreamReader(in));
            String line;
            while((line = br.readLine()) != null) {
                
                //System.out.println(line);
                r.add(line);

            }

   System.out.println(r.toString());
            return sr;
        } catch (IOException e) {
    
            e.printStackTrace();
        } 


        
        return sr;
       
	}


	       	    

	    /*
	     * Start z3.
	     *
	     * Add parameters here ...
	     */
	    private Process buildProcess() throws IOException {
	        ProcessBuilder pb = new ProcessBuilder("z3", "-T:3", "-in", "-smt2");
	        return pb.start();
	    }

	

}
