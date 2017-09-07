/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.integration;

import static org.junit.Assert.assertEquals;

import java.io.InputStream;
import java.util.ArrayList;
import java.util.List;

import org.junit.Test;

import edu.kit.iti.algover.parser.DafnyTree;
import edu.kit.iti.algover.parser.ParserTest;
import edu.kit.iti.algover.project.Project;
import edu.kit.iti.algover.proof.PVC;
import edu.kit.iti.algover.proof.ProofFormula;
import edu.kit.iti.algover.smt.Z3Solver;
import edu.kit.iti.algover.term.Sequent;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.term.builder.TermBuilder;
import edu.kit.iti.algover.util.TestUtil;

/**
 * This is only the first round of integration tests. As soon as proof replaying
 * works this has to be extended.
 */
public class IntegrationTest1 {


    @Test
    public void sumAndMax() throws Exception {

        InputStream stream = ParserTest.class.getResourceAsStream("full/sumandmax.dfy");
        DafnyTree fileTree = ParserTest.parseFile(stream);

        // performs type analysis etc:
        Project project = TestUtil.mockProject(fileTree);

        List<PVC> pvcs = project.generateAndCollectPVC().getContents();

        for (PVC pvc : pvcs) {
            Sequent sequent = pvc.getSequent();
            Z3Solver z3 = new Z3Solver(project, pvc.getSymbolTable());
            TermBuilder tb = new TermBuilder(pvc.getSymbolTable());

            List<Term> formulae = new ArrayList<>();
            for (ProofFormula formula : sequent.getAntecedent()) {
                formulae.add(formula.getTerm());
            }
            for (ProofFormula formula : sequent.getSuccedent()) {
                formulae.add(tb.negate(formula.getTerm()));
            }

            if (TestUtil.VERBOSE) {
                String smt = z3.createSMTInput(formulae);
                System.out.println(smt);//TestUtil.prettyPrintSMT(smt));
            }

            assertEquals("unsat", z3.solve(formulae));
        }

    }

}
