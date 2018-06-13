package edu.kit.iti.algover.smttrans.access;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.OutputStream;
import java.util.ArrayList;
import java.util.List;

public class CVCAccess extends SolverAccess {

    @Override
    public SolverResponse accessSolver(String smt) {
        Process process;

        try {
            process = buildProcess();

            OutputStream out = process.getOutputStream();
            InputStream in = process.getInputStream();
            //out.write(debugsmt.getBytes());
            out.write(smt.getBytes());
            out.write("(check-sat)".getBytes());
            out.write("(get-model)".getBytes());
            out.close();
            List<String> data = new ArrayList<>();
            BufferedReader br = new BufferedReader(new InputStreamReader(in));
            String line;
            while ((line = br.readLine()) != null) {
                // System.out.println(line);
                data.add(line);
            }
            
            if(data.isEmpty())
                return new SolverResponse(Response.ERROR);
            System.out.println(data);
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
        ProcessBuilder pb = new ProcessBuilder("cvc4", "--lang smt"); //, "-in", "-smt2"
        return pb.start();
    }




    

}
