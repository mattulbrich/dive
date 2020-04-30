/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.util;

import edu.kit.iti.algover.dafnystructures.DafnyFile;
import edu.kit.iti.algover.data.BuiltinSymbols;
import edu.kit.iti.algover.data.SymbolTable;
import edu.kit.iti.algover.parser.DafnyException;
import edu.kit.iti.algover.parser.DafnyParserException;
import edu.kit.iti.algover.project.Project;
import edu.kit.iti.algover.proof.MockPVCBuilder;
import edu.kit.iti.algover.proof.PVC;
import edu.kit.iti.algover.proof.Proof;
import edu.kit.iti.algover.proof.ProofFormula;
import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.term.ApplTerm;
import edu.kit.iti.algover.term.Sequent;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.term.builder.TermBuildException;
import edu.kit.iti.algover.term.builder.TermBuilder;
import edu.kit.iti.algover.term.parser.TermParser;
import org.antlr.runtime.RecognitionException;
import org.junit.AfterClass;
import org.junit.BeforeClass;

import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;
import java.util.stream.Collectors;

// consider merging into TestUtil.
public class ProofMockUtil {

    public static Term TRUE;
    public static Term FALSE;

    private static Project project;

    static {
        try {
            TRUE = new ApplTerm(BuiltinSymbols.TRUE);
            FALSE = new ApplTerm(BuiltinSymbols.FALSE);
        } catch (TermBuildException e) {
            e.printStackTrace();
        }
    }

    /**
     * Create a mocked proof node from a parent and the sequent data.
     *
     * @param parent          the parent node
     * @param antedecentTerms antecedent formulas
     * @param succedentTerms  succedent formulas
     * @return a new proof node
     * @throws TermBuildException if formulas are not boolean
     */
    @TestInfrastructure
    public static ProofNode mockProofNode(ProofNode parent, Term[] antedecentTerms, Term[] succedentTerms) throws TermBuildException {
        List<ProofFormula> antedecentFormulas = new ArrayList<>(antedecentTerms.length);
        for (int i = 0; i < antedecentTerms.length; i++) {
            antedecentFormulas.add(new ProofFormula(antedecentTerms[i]));
        }
        List<ProofFormula> succedentFormulas = new ArrayList<>(succedentTerms.length);
        for (int i = 0; i < succedentTerms.length; i++) {
            succedentFormulas.add(new ProofFormula(succedentTerms[i]));
        }
        return mockProofNode(parent, antedecentFormulas, succedentFormulas);
    }


    /**
     * Create a mocked proof node from a parent and the sequent data.
     *
     * @param parent          the parent node
     * @param antedecentTerms antecedent formulas
     * @param succedentTerms  succedent formulas
     * @return a new proof node
     * @throws TermBuildException if formulas are not boolean
     */
    @TestInfrastructure
    public static ProofNode mockProofNode(ProofNode parent, ProofFormula[] antedecentTerms, ProofFormula[] succedentTerms) throws TermBuildException {
        List<ProofFormula> antedecentFormulas = new ArrayList<>(antedecentTerms.length);
        antedecentFormulas.addAll(Arrays.asList(antedecentTerms));
        List<ProofFormula> succedentFormulas = new ArrayList<>(succedentTerms.length);
        succedentFormulas.addAll(Arrays.asList(succedentTerms));
        return mockProofNode(parent, antedecentFormulas, succedentFormulas);
    }

    /**
     * Create a mocked proof node from a parent and the sequent data.
     *
     * @param parent          the parent node
     * @param antedecentTerms antecedent formulas
     * @param succedentTerms  succedent formulas
     * @return a new proof node
     * @throws TermBuildException if formulas are not boolean
     */
    @TestInfrastructure
    public static ProofNode mockProofNode(ProofNode parent, List<ProofFormula> antedecentTerms, List<ProofFormula> succedentTerms) throws TermBuildException {
        return new ProofNode(parent, null, null, null,
                new Sequent(antedecentTerms, succedentTerms), null);
    }

    /**
     * Make a proof for a formula that serves as the only succedent formula.
     *
     * @param termStr the formula to parse
     * @return a fresh mock proof object
     */
    @TestInfrastructure
    public static Proof makeProof(String termStr) throws DafnyParserException, IOException, RecognitionException, DafnyException {
        return makeProof(new BuiltinSymbols(), termStr);
    }

    /**
     * Make a proof for a formula that serves as the only succedent formula.
     *
     * @param termStr     the formula to parse
     * @param symboltable the table to use
     * @return a fresh mock proof object
     */
    @TestInfrastructure
    public static Proof makeProof(SymbolTable symboltable, String termStr) throws DafnyParserException, DafnyException, IOException, RecognitionException {
        Term term = TermParser.parse(symboltable, termStr);
        Sequent sequent = Sequent.singleSuccedent(new ProofFormula(term));
        return makeProof(symboltable, sequent);
    }

    /**
     * Make a proof for a sequent.
     *
     * @param sequent the sequent to use as root
     * @return a fresh mock proof object
     */
    @TestInfrastructure
    public static Proof makeProof(Sequent sequent) throws DafnyParserException, RecognitionException, IOException, DafnyException {
        return makeProof(new BuiltinSymbols(), sequent);
    }

    /**
     * Make a proof for a sequent.
     *
     * @param sequent the sequent to use as root
     * @param symboltable the table to use
     * @return a fresh mock proof object
     */
    @TestInfrastructure
    public static Proof makeProof(SymbolTable symboltable, Sequent sequent) throws DafnyParserException, DafnyException, RecognitionException, IOException {
        if(project == null) {
            project = TestUtil.mockProject("method m() ensures true {}");
        }
        MockPVCBuilder pb = new MockPVCBuilder();
        pb.setDeclaration(project.getMethod("m"));
        pb.setSymbolTable(symboltable);
        pb.setSequent(sequent);
        pb.setPathIdentifier("test");
        pb.setReferenceMap(Collections.emptyMap());
        PVC pvc = pb.build();
         List<DafnyFile> dfyFiles = project.getDafnyFiles().stream().filter(dafnyFile -> dafnyFile.getFilename().equals(pvc.getDeclaration().getFilename())).collect(Collectors.toList());
            if(dfyFiles.size()>0) {
                return new Proof(project, pvc, dfyFiles.get(0));
            } else {
                return new Proof(project, pvc, null);
            }
    }

    /**
     * Make a proof for a sequent.
     *
     * @param sequent the sequent to use as root
     * @param symboltable the table to use
     * @return a fresh mock proof object
     */
    @TestInfrastructure
    public static Proof makeProofWithRoot(SymbolTable symboltable, Sequent sequent) throws DafnyParserException, DafnyException, RecognitionException, IOException {
        if(project == null) {
            project = TestUtil.mockProject("method m() ensures true {}");
        }
        MockPVCBuilder pb = new MockPVCBuilder();
        pb.setDeclaration(project.getMethod("m"));
        pb.setSymbolTable(symboltable);
        pb.setSequent(sequent);
        pb.setPathIdentifier("test");
        pb.setReferenceMap(Collections.emptyMap());
        PVC pvc = pb.build();
        List<DafnyFile> dfyFiles = project.getDafnyFiles().stream().filter(dafnyFile -> dafnyFile.getFilename().equals(pvc.getDeclaration().getFilename())).collect(Collectors.toList());
        Proof p;
        if(dfyFiles.size()>0) {
            p =  new Proof(project, pvc, dfyFiles.get(0));
        } else {
            p = new Proof(project, pvc, null);
        }
        p.setScriptTextAndInterpret("");
        return p;
    }
    
    /**
     * Create a mocked proof node from a parent and a sequent.
     *
     * @param parent          the parent node
     * @param s               the sequent
     * @return a new proof node
     * @throws TermBuildException if formulas are not boolean
     */
    @TestInfrastructure
    public static ProofNode mockProofNode(ProofNode parent, Sequent s) throws TermBuildException {
        return mockProofNode(parent, s.getAntecedent(), s.getSuccedent());
    }

    @TestInfrastructure
    public static ProofNode mockProofNode(Sequent s) throws TermBuildException {
        return mockProofNode(null, s);
    }


    @TestInfrastructure
    public static ProofNode mockProofNode(Sequent seq, PVC pvc) {
        return new ProofNode(null, null, null, null, seq, pvc);
    }
}
