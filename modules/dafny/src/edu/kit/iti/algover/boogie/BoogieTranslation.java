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

    private final Project project;
    private Sequent sequent;
    private SymbolTable symbolTable;
    private @Nullable CharSequence obligation;

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

    private CharSequence produceObligation() throws TermBuildException {

        assert symbolTable != null;
        assert sequent != null;

        TermBuilder tb = new TermBuilder(symbolTable);

        List<String> clauses = new ArrayList<>();

        BoogieVisitor v = new BoogieVisitor();
        BoogieFunctionDefinitionVisitor fdv = new BoogieFunctionDefinitionVisitor();

        v.addClassDeclarations(project);

        for (ProofFormula formula : sequent.getAntecedent()) {
            Term term = formula.getTerm();
            term = LetInlineVisitor.inline(term);
            term = fdv.collectAndMask(term);
            // term = NothingResolution.resolveNothing(term);
            String translation = term.accept(v, null);
            clauses.add(translation);
        }

        for (ProofFormula formula : sequent.getSuccedent()) {
            Term term = formula.getTerm();
            term = LetInlineVisitor.inline(term);
            term = fdv.collectAndMask(term);
            // term = NothingResolution.resolveNothing(term);
            term = tb.negate(term);
            String translation = term.accept(v, null);
            clauses.add(translation);
        }

        fdv.findFunctionDefinitions(symbolTable);
        fdv.getFunctionDefinitions(v);

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

    public CharSequence getObligation() throws TermBuildException {

        if (obligation != null) {
            return obligation;
        }

        CharSequence sb = this.produceObligation();

        this.obligation = sb;
        return sb;
    }

    public String getHash() throws TermBuildException, NoSuchAlgorithmException {
        MessageDigest digest = MessageDigest.getInstance("SHA-256");
        byte[] hash = digest.digest(getObligation().toString().getBytes());
        return Base64.getEncoder().encodeToString(hash);
    }

    public Sequent getSequent() {
        return sequent;
    }

    public void setSequent(Sequent sequent) {
        this.sequent = sequent;
        this.obligation = null;
    }

    public SymbolTable getSymbolTable() {
        return symbolTable;
    }

    public void setSymbolTable(SymbolTable symbolTable) {
        this.symbolTable = symbolTable;
        this.obligation = null;
    }
}
