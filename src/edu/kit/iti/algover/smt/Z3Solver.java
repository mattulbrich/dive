package edu.kit.iti.algover.smt;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.OutputStream;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import edu.kit.iti.algover.data.SymbolTable;
import edu.kit.iti.algover.term.FunctionSymbol;
import edu.kit.iti.algover.term.Sort;
import edu.kit.iti.algover.term.Term;

public class Z3Solver {

    public static final String COMMAND = "/usr/bin/z3";

    enum Result { VALID, UNKNOWN, NEGSAT }

    private final SMTTrans smtTrans = new SMTTrans();
    private SymbolTable symbolTable;

    public List<Result> solve(Collection<Term> formulae) throws IOException {

        Process process = buildProcess();
        try {
            OutputStream out = process.getOutputStream();
            InputStream in = process.getInputStream();

            out.write(createSMTInputput(formulae).getBytes());
            out.close();

            List<Result> result = new ArrayList<>();
            BufferedReader br = new BufferedReader(new InputStreamReader(in));
            String line;
            while((line = br.readLine()) != null) {
                switch(line) {
                case "unsat":
                    result.add(Result.VALID);
                    break;
                case "sat":
                    result.add(Result.NEGSAT);
                    break;
                case "unkown":
                    result.add(Result.UNKNOWN);
                    break;
                }
            }

            return result;
        } finally {
            process.destroy();
        }
    }

    public Z3Solver(SymbolTable symbolTable) {
        this.symbolTable = symbolTable;
    }

    public String createSMTInputput(Collection<Term> formulae) throws IOException {

        StringBuilder sb = new StringBuilder();

        sb.append("; Declarations \n\n");
        for (FunctionSymbol fs: symbolTable.getAllSymbols()) {
            if(!fs.getName().contains("$") && !fs.getName().matches("[0-9]+")) {
                sb.append(makeDecl(fs)).append("\n");
            }
        }

        sb.append("\n; Proof verification condition\n");

        for (Term pc : formulae) {
            sb.append("; Formula " + pc + "\n");

            sb.append("(assert ");
            sb.append(smtTrans.trans(pc));
            sb.append(")\n\n");
        }
        sb.append("(check-sat)\n");

        return sb.toString();
    }

    private SExpr makeDecl(FunctionSymbol fs) {
        SExpr name = new SExpr(fs.getName());

        SExpr result = SMTTrans.typeToSMT(fs.getResultSort());

        List<SExpr> argList = new ArrayList<>();
        for (Sort argSort : fs.getArgumentSorts()) {
            argList.add(SMTTrans.typeToSMT(argSort));
        }
        SExpr args = new SExpr(argList);

        return new SExpr("declare-fun", name, new SExpr(args), result);
    }

    private Process buildProcess() throws IOException {
        ProcessBuilder pb = new ProcessBuilder(COMMAND, "-t:20", "-in", "-smt2");
        return pb.start();
    }
}
