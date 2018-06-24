package edu.kit.iti.algover.smttrans.access;

import java.io.BufferedReader;

import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.OutputStream;
import java.util.ArrayList;

import java.util.List;

public class Z3Access extends SolverAccess {

    @Override
    public SolverResponse accessSolver(SolverParameter p) {

        Process process;
        String smt = p.getSMT();
        try {
            process = buildProcess(p);

            OutputStream out = process.getOutputStream();
            InputStream in = process.getInputStream();

            out.write(smt.getBytes());
            out.write("(check-sat)".getBytes());
            out.write("(get-model)".getBytes());
            out.close();
            List<String> data = new ArrayList<>();
            BufferedReader br = new BufferedReader(new InputStreamReader(in));
            String line;
            int balance = 0;
            String expr = "";
            while ((line = br.readLine()) != null) {
                // System.out.println(line);
                if (line.replaceAll("\\s+", "").toLowerCase().equals("(model"))
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
          //  System.out.println(data);
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
    private Process buildProcess(SolverParameter p) throws IOException {
        ProcessBuilder pb = new ProcessBuilder("z3", "-T:" + p.getTimeout(), "-in", "-smt2");
        return pb.start();
    }

}
