/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 *
 */

package edu.kit.iti.algover.boogie;

import edu.kit.iti.algover.data.SymbolTable;
import edu.kit.iti.algover.project.Project;
import edu.kit.iti.algover.proof.ProofFormula;
import edu.kit.iti.algover.rules.RuleException;
import edu.kit.iti.algover.smt.SMTSolver.Result;
import edu.kit.iti.algover.term.Sequent;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.term.builder.LetInlineVisitor;
import edu.kit.iti.algover.term.builder.TermBuilder;
import edu.kit.iti.algover.util.Util;

import java.io.BufferedReader;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.OutputStream;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Set;

public class BoogieProcess {

    /**
     * The command by which z3 is invoked.
     */
    public static final String COMMAND =
            System.getProperty("edu.kit.iti.algover.boogie_binary", "boogie");

    private final static String PRELUDE = loadPrelude();
    private Project project;

    public BoogieProcess(Project project) {
        this.project = project;
    }

    private static String loadPrelude() {
        try {
            InputStream is = BoogieProcess.class.getResourceAsStream("DafnyPrelude.bpl");
            if(is == null) {
                throw new FileNotFoundException("DafnyPrelude.bpl");
            }
            return Util.streamToString(is);
        } catch (IOException e) {
            throw new RuntimeException(e);
        }
    }

    private Sequent sequent;
    private SymbolTable symbolTable;
    private String additionalBoogieText = "";

    public CharSequence produceObligation() throws Exception {

        assert symbolTable != null;
        assert sequent != null;

        TermBuilder tb = new TermBuilder(symbolTable);

        List<String> clauses = new ArrayList<>();

        BoogieVisitor v = new BoogieVisitor();

        v.addClassDeclarations(project);

        for (ProofFormula formula : sequent.getAntecedent()) {
            Term term = formula.getTerm();
            term = LetInlineVisitor.inline(term);
           // term = NothingResolution.resolveNothing(term);
            String translation = term.accept(v, null);
            clauses.add(translation);
        }

        for (ProofFormula formula : sequent.getSuccedent()) {
            Term term = formula.getTerm();
            term = LetInlineVisitor.inline(term);
           // term = NothingResolution.resolveNothing(term);
            term = tb.negate(term);
            String translation = term.accept(v, null);
            clauses.add(translation);
        }

        StringBuilder sb = new StringBuilder();
        sb.append(Util.join(v.getDeclarations(), "\n")).append("\n\n");
        sb.append(Util.join(v.getAxioms(), "\n")).append("\n\n");
        sb.append("procedure Sequent()\n  ensures false;\n{\n");
        for (String clause : clauses) {
            sb.append("  assume " + clause + ";\n");
        }
        sb.append("}");

        return sb;
    }

    public boolean callBoogie() throws Exception {

        CharSequence sb = produceObligation();

        Path tmpFile = Files.createTempFile("AlgoVer", ".bpl");
        Files.write(tmpFile, Arrays.asList(PRELUDE, sb, additionalBoogieText));

        Process process = buildProcess(tmpFile);
        InputStream in = process.getInputStream();

        BufferedReader br = new BufferedReader(new InputStreamReader(in));
        String line;
        while ((line = br.readLine()) != null) {
            System.out.println(" < " + line);
            if (line.startsWith("Boogie program verifier finished with 1 verified"))
                return true;
            if (line.startsWith("Boogie program verifier finished with 0 verified"))
                return false;
        }

        throw new RuleException("Oh dear, boogie seems to fail");
    }

    private Process buildProcess(Path tmpFile) throws IOException {
        ProcessBuilder pb =
                new ProcessBuilder(COMMAND, tmpFile.toString());
        return pb.start();
    }

    public String getAdditionalBoogieText() {
        return additionalBoogieText;
    }

    public void setAdditionalBoogieText(String additionalBoogieText) {
        this.additionalBoogieText = additionalBoogieText;
    }

    public void setSequent(Sequent sequent) {
        this.sequent = sequent;
    }

    public Sequent getSequent() {
        return sequent;
    }

    public void setSymbolTable(SymbolTable symbolTable) {
        this.symbolTable = symbolTable;
    }

    public SymbolTable getSymbolTable() {
        return symbolTable;
    }
}
