package edu.kit.iti.algover.smt;

import java.io.IOException;

import edu.kit.iti.algover.PathCondition;
import edu.kit.iti.algover.SymbexState;
import edu.kit.iti.algover.parser.PseudoTree;

public class Z3Solver {

    public static final String COMMAND = "z3";

    enum Result { VALID, UNKNOWN, COUNTEREX, NEGSAT }

    private SMTTrans smtTrans = new SMTTrans();

//    public List<Result> solve(SymbexState obligation) throws IOException {
//
//        Process process = buildProcess();
//        try {
//            OutputStream out = process.getOutputStream();
//            InputStream in = process.getInputStream();
//
//            out.write(createSMTInputput(obligation).getBytes());
//        } finally {
//            process.destroy();
//        }
//
//    }

    public String createSMTInputput(SymbexState obligation) throws IOException {

        StringBuilder sb = new StringBuilder();

        // TODO ADD DECLARATIONS!

        for (PathCondition pc : obligation.getPathConditions()) {
            sb.append("(assert ");
            sb.append(smtTrans.trans(pc.getInstantiatedExpression()));
            sb.append(")\n\n");
        }

        sb.append("(push)\n");

        for (PseudoTree pc : obligation.getProofObligations()) {
            sb.append("(assert ");
            sb.append(smtTrans.trans(obligation.getMap().instantiate(pc.getLastChild())));
            sb.append(")\n\n");
            sb.append("(check-sat)(pop)(push)\n");
        }

        return sb.toString();
    }

    private Process buildProcess() throws IOException {
        ProcessBuilder pb = new ProcessBuilder(COMMAND, "-t:20");
        return pb.start();
    }
}
