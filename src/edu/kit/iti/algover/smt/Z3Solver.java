package edu.kit.iti.algover.smt;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.OutputStream;
import java.util.ArrayList;
import java.util.List;

import edu.kit.iti.algover.ProgramDatabase;
import edu.kit.iti.algover.parser.DafnyParser;
import edu.kit.iti.algover.parser.DafnyTree;
import edu.kit.iti.algover.symbex.PathConditionElement;
import edu.kit.iti.algover.symbex.SymbexState;

public class Z3Solver {

    public static final String COMMAND = "/usr/bin/z3";

    enum Result { VALID, UNKNOWN, NEGSAT }

    private final SMTTrans smtTrans = new SMTTrans();
    private final ProgramDatabase programDatabase;

    public List<Result> solve(SymbexState obligation) throws IOException {

        Process process = buildProcess();
        try {
            OutputStream out = process.getOutputStream();
            InputStream in = process.getInputStream();

            out.write(createSMTInputput(obligation).getBytes());
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

    public Z3Solver(ProgramDatabase programDatabase) {
        this.programDatabase = programDatabase;
        // TODO Auto-generated constructor stub
    }

    public String createSMTInputput(SymbexState obligation) throws IOException {

        StringBuilder sb = new StringBuilder();

        DafnyTree function = obligation.getFunction();
        sb.append("; Args\n");
        extractDeclarations(sb,
                function.getFirstChildWithType(DafnyParser.ARGS).
                    getChildrenWithType(DafnyParser.VAR));

        sb.append("; Returns\n");
        extractDeclarations(sb,
                function.getFirstChildWithType(DafnyParser.RETURNS).
                    getChildrenWithType(DafnyParser.VAR));

        sb.append("; Variables\n");
        extractDeclarations(sb, ProgramDatabase.getAllVariableDeclarations(function.getLastChild()));

        sb.append("; Skolems\n");
        extractSkolemVars(sb, obligation);

        sb.append("; Path condition\n");
        for (PathConditionElement pc : obligation.getPathConditions()) {
            sb.append("(assert ");
            sb.append(smtTrans.trans(pc.getInstantiatedExpression()));
            sb.append(")\n");
        }

        sb.append("; Proof obligations\n");
        sb.append("(push)\n");

        for (DafnyTree pc : obligation.getProofObligations()) {
            sb.append("(assert (not ");
            sb.append(smtTrans.trans(obligation.getMap().instantiate(pc.getLastChild())));
            sb.append("))\n");
            sb.append("(check-sat)(pop)(push)\n");
        }

        return sb.toString();
    }

    private void extractSkolemVars(StringBuilder sb, SymbexState obligation) {
        for(String anon : obligation.getMap().findAnonymisingConsts()) {
            assert anon.contains("#");
            // get name from m#1
            String name = anon.substring(0, anon.indexOf("#"));
            // ask database to get declaration for m
            DafnyTree decl = programDatabase.getVariableDeclaration(obligation.getFunction(), name);
            if(decl == null) {
                throw new RuntimeException("Undefined symbol " + name);
            }
            // type of decl
            String type = smtTrans.transToType(decl.getLastChild());
            // declare const with same type as m
            sb.append("(declare-const ").append(anon.replace('#', '$')).append(" ").append(type)
                .append(")\n");
        }
    }

    protected void extractDeclarations(StringBuilder sb, List<DafnyTree> decls) {
        if(decls == null) {
            return;
        }
        for (DafnyTree decl : decls) {
            assert decl.getType() == DafnyParser.VAR;
            String name = decl.getChild(0).getToken().getText();
            String type = smtTrans.transToType(decl.getChild(1));
            sb.append("(declare-const ").append(name).append("$pre ").append(type).append(")\n");
        }
    }

    private Process buildProcess() throws IOException {
        ProcessBuilder pb = new ProcessBuilder(COMMAND, "-t:20", "-in", "-smt2");
        return pb.start();
    }
}
