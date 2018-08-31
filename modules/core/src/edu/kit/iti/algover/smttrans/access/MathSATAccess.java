package edu.kit.iti.algover.smttrans.access;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.OutputStream;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

public class MathSATAccess extends SolverAccess {

    @Override
    public SolverResponse accessSolver(SolverParameter p) {

        String smt = p.getSMT();
        try {

            File f = File.createTempFile("file", ".smt2");
            BufferedWriter bw = new BufferedWriter(new FileWriter(f));
            bw.write(smt);

            bw.write("(check-sat)");

            bw.close();
            Runtime rt = Runtime.getRuntime();

            Process process = rt.exec("mathsat -input=smt2 " + f.getAbsolutePath());

            InputStream in = process.getInputStream();

            List<String> data = new ArrayList<>();
            BufferedReader br = new BufferedReader(new InputStreamReader(in));
            String line;
            while ((line = br.readLine()) != null) {
                System.out.println(line);
                data.add(line);
            }

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

}
