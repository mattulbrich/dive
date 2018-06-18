package edu.kit.iti.algover.smttrans.access;

import java.io.BufferedReader;

import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.OutputStream;
import java.util.ArrayList;

import java.util.List;

public class Z3Access extends SolverAccess {

    // public String debugsmt = "(declare-sort X)(declare-sort Heap)(declare-sort
    // Field 2)(declare-fun fieldstoreXInt (Heap X (Field X Int) Int)
    // Heap)(declare-fun fieldselectXInt (Heap X (Field X Int)) Int)(declare-const
    // heap Heap)(declare-const X.y (Field X Int))(declare-const nullX
    // X)(declare-const o X)(assert (not (= o nullX)))(assert (= heap
    // (fieldstoreXInt heap o X.y 8)))(assert (> (fieldselectXInt heap o X.y) 5))";
    public String debugsmt = "\r\n" + "      (declare-sort Heap)\r\n" + "      (declare-sort ArrInt)\r\n"
            + "      (declare-const heap Heap)\r\n" + "      (declare-const null.1 ArrInt)\r\n"
            + "      (declare-const a.1 ArrInt)\r\n" + "      (declare-const max.1 Int)\r\n"
            + "      (declare-const i.1 Int)\r\n" + "      (declare-const k.1 Int)\r\n"
            + "      (declare-fun  arrselectInt (Heap ArrInt Int) Int)\r\n"
            + "      (declare-fun  arrstoreInt (Heap ArrInt Int Int) Heap)\r\n"
            + "      (declare-fun arrlenInt (ArrInt) Int)\r\n" + "      (assert\r\n" + "      (forall\r\n"
            + "      (\r\n" + "          (i Int)\r\n" + "          (h Heap)\r\n" + "          (a ArrInt)\r\n"
            + "          (v Int)\r\n" + "      )\r\n" + "      (!\r\n"
            + "          (= (arrselectInt (arrstoreInt h a i v) a i) v) :pattern((arrstoreInt h a i v))\r\n"
            + "      )))\r\n" + "     \r\n" + "      (assert (not (= a.1 null.1)))\r\n"
            + "      (assert (>= (arrlenInt a.1) 1))\r\n" + "      (assert (= max.1 (arrselectInt heap a.1 0)))\r\n"
            + "      (assert(= i.1 1))\r\n"
            + "      (assert(not(forall((k.1 Int))(=> (and (<= 0 k.1) (< k.1 i.1)) (<= (arrselectInt heap a.1 k.1) max.1)))))";

    
    public String d2 = "    (declare-sort X)\r\n" + 
            "    (declare-sort Heap)\r\n" + 
            "    (declare-sort Field 2)\r\n" + 
            "    (declare-fun fieldstoreXInt (Heap X (Field X Int) Int) Heap)\r\n" + 
            "    (declare-fun fieldselectXInt (Heap X (Field X Int)) Int)\r\n" + 
            "    (declare-const heap Heap)\r\n" + 
            "    (declare-const X.y (Field X Int))\r\n" + 
            "    (declare-const nullX X)\r\n" + 
            "    (declare-const o X)\r\n" + 
            "    (assert (not (= o nullX)))\r\n" + 
            "    (assert (= heap (fieldstoreXInt heap o X.y 8)))\r\n" + 
            "    (assert (> (fieldselectXInt heap o X.y) 5))";
    
    
    public String d3 = "(declare-const a Int)\r\n" + 
            "(declare-const b Int)\r\n" + 
            "(declare-const c Int)\r\n" + 
            "(declare-const d Int)\r\n" + 
            "\r\n" + 
            "(define-fun getSum ((x!1 Int) (x!2 Int) (x!3 Int) (x!4 Int)) Int\r\n" + 
            "   (+ a b c d)\r\n" + 
            ")\r\n" + 
            "(assert (> a 0))\r\n" + 
            "(assert (> b 0))\r\n" + 
            "(assert (> c 0))\r\n" + 
            "(assert (not(> (getSum a b c d) 0)))";
    
    @Override
    public SolverResponse accessSolver(String smt) {

        Process process;

        try {
            process = buildProcess();

            OutputStream out = process.getOutputStream();
            InputStream in = process.getInputStream();
            //out.write(debugsmt.getBytes());
            out.write(smt.getBytes());
           // out.write(d3.getBytes());
            out.write("(check-sat)".getBytes());
            out.write("(get-model)".getBytes());
            out.close();
            List<String> data = new ArrayList<>();
            BufferedReader br = new BufferedReader(new InputStreamReader(in));
            String line;
            int balance = 0;
            String expr = "";
            while ((line = br.readLine()) != null) {    
//                                                  System.out.println(line);                 
                if(line.replaceAll("\\s+","").toLowerCase().equals("(model"))
                    continue;
                // System.out.println(line);
                balance -= line.length() - line.replace("(", "").length();
                balance += line.length() - line.replace(")", "").length();
                expr += line;
                if (balance == 0) {
                    data.add(expr.trim());
                    expr = "";
            
                }
            }
            System.out.println(data);
            if (data.isEmpty())
                return new SolverResponse(Response.ERROR);
            
            if (data.get(0).toLowerCase().contains("unsat")) {
                return new SolverResponse(Response.UNSAT);
            }
            if (data.get(0).toLowerCase().contains("sat")) {
                return new SolverResponse(Response.SAT, new Model(data.subList(1, data.size())));
            }
            if (data.get(0).toLowerCase().contains("unknown")) {
                return new SolverResponse(Response.UNKNOWN);
            }

        } catch (IOException e) {
            e.printStackTrace();
            return new SolverResponse(Response.ERROR);
        }

        return new SolverResponse(Response.ERROR);

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
