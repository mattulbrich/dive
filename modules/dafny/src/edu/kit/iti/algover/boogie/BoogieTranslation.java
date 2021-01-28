/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2020 Karlsruhe Institute of Technology
 *
 */

package edu.kit.iti.algover.boogie;

import edu.kit.iti.algover.data.SymbolTable;
import edu.kit.iti.algover.project.Project;
import edu.kit.iti.algover.proof.ProofFormula;
import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.term.Sequent;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.term.builder.LetInlineVisitor;
import edu.kit.iti.algover.term.builder.TermBuildException;
import edu.kit.iti.algover.term.builder.TermBuilder;
import edu.kit.iti.algover.util.Util;
import nonnull.Nullable;

import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.InputStream;
import java.security.MessageDigest;
import java.security.NoSuchAlgorithmException;
import java.util.ArrayList;
import java.util.Base64;
import java.util.Collections;
import java.util.List;

/**
 * A class responsible for translating a sequent into a Boogie source code.
 *
 * @author Mattias Ulbrich
 */
public class BoogieTranslation {

    private static final String DAFNYPRELUDE_RESOURCE = "DafnyPrelude.bpl";

    /**
     * The part which is the same for all translations.
     * It is not included in {@link #getObligation()} but must be added to
     * the boogie transcript before the obligation.
     */
    public final static String PRELUDE = loadPrelude();
    public final static int PRELUDE_LINE_COUNT = PRELUDE.split("\n").length + 1;

    private final Project project;
    private ProofNode proofNode;
    private SymbolTable symbolTable;
    private @Nullable List<String> obligation;
    private boolean verified;
    private int suffix = -1;

    public BoogieTranslation(Project project) {
        this.project = project;
    }

    private static String loadPrelude() {
        try {
            InputStream is = BoogieProcess.class.getResourceAsStream(DAFNYPRELUDE_RESOURCE);
            if(is == null) {
                throw new FileNotFoundException(DAFNYPRELUDE_RESOURCE);
            }
            return Util.streamToString(is);
        } catch (IOException e) {
            throw new RuntimeException(e);
        }
    }

    private List<String> produceObligation() throws TermBuildException {

        assert symbolTable != null;
        assert proofNode != null;

        TermBuilder tb = new TermBuilder(symbolTable);

        List<String> clauses = new ArrayList<>();

        BoogieVisitor v = new BoogieVisitor();
        BoogieFunctionDefinitionVisitor fdv = new BoogieFunctionDefinitionVisitor();

        v.setSuffix(suffix);
        v.addClassDeclarations(project);

        for (ProofFormula formula : proofNode.getSequent().getAntecedent()) {
            Term term = formula.getTerm();
            term = LetInlineVisitor.inline(term);
            term = fdv.collectAndMask(term);
            // term = NothingResolution.resolveNothing(term);
            String translation = term.accept(v, null);
            clauses.add(translation);
        }

        for (ProofFormula formula : proofNode.getSequent().getSuccedent()) {
            Term term = formula.getTerm();
            term = LetInlineVisitor.inline(term);
            term = fdv.collectAndMask(term);
            // term = NothingResolution.resolveNothing(term);
            term = tb.negate(term);
            String translation = term.accept(v, null);
            clauses.add(translation);
        }

        fdv.findFunctionDefinitions(symbolTable, v);


        List<String> result = new ArrayList<>();
        result.addAll(v.getDeclarations());
        result.add("");
        StringBuilder sb = new StringBuilder();
        sb.append("procedure Sequent");
        if (suffix != -1) {
            sb.append("_" + suffix);
        }
        sb.append("()");
        result.add(sb.toString());
        result.add("  ensures false;");
        result.add("{");
        for (String axiom : v.getAxioms()) {
            result.add("  assume " + axiom + ";");
        }
        for (String clause : clauses) {
            result.add("  assume " + clause + ";");
        }
        result.add("}");
        result.add("");

        return result;
    }

    public List<String> getObligation() throws TermBuildException {

        if (obligation != null) {
            return obligation;
        }

        this.obligation = Collections.unmodifiableList(this.produceObligation());
        return this.obligation;
    }

    public String getHash() throws TermBuildException, NoSuchAlgorithmException {
        MessageDigest digest = MessageDigest.getInstance("SHA-256");
        byte[] hash = digest.digest(getObligation().toString().getBytes());
        return Base64.getEncoder().encodeToString(hash);
    }

    public SymbolTable getSymbolTable() {
        return symbolTable;
    }

    public void setSymbolTable(SymbolTable symbolTable) {
        this.symbolTable = symbolTable;
        this.obligation = null;
    }

    public void setProofNode(ProofNode proofNode) {
        this.proofNode = proofNode;
    }

    public void setSuffix(int suffix) {
        this.suffix = suffix;
    }

    public void setVerified(boolean b) {
        this.verified = b;
    }

    public boolean isVerified() {
        return verified;
    }
}
