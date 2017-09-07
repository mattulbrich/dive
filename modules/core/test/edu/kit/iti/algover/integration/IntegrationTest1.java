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
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;

import edu.kit.iti.algover.parser.DafnyTree;
import edu.kit.iti.algover.parser.ParserTest;
import edu.kit.iti.algover.project.Project;
import edu.kit.iti.algover.proof.PVC;
import edu.kit.iti.algover.proof.ProofFormula;
import edu.kit.iti.algover.smt.SMTSolver.Result;
import edu.kit.iti.algover.smt.Z3Solver;
import edu.kit.iti.algover.term.Sequent;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.term.builder.TermBuilder;
import edu.kit.iti.algover.util.TestUtil;

/**
 * This is only the first round of integration tests. As soon as proof replaying
 * works this has to be extended.
 */
@RunWith(Parameterized.class)
public class IntegrationTest1 {

    private PVC pvc;
    private Project project;

    public IntegrationTest1(String name, PVC pvc, Project project) {
        this.pvc = pvc;
        this.project = project;
    }

    @Parameters(name= "{0}")
    public static Iterable<Object[]> data() throws Exception {

        InputStream stream = ParserTest.class.getResourceAsStream("full/sumandmax.dfy");
        DafnyTree fileTree = ParserTest.parseFile(stream);

        // performs type analysis etc:
        Project project = TestUtil.mockProject(fileTree);

        List<PVC> pvcs = project.generateAndCollectPVC().getContents();

        List<Object[]> result = new ArrayList<>();
        for (PVC pvc : pvcs) {
            result.add(new Object[] { pvc.getName(), pvc, project});
        }

        return result;
    }

    @Test
    public void testZ3Verification() throws Exception {

        Sequent sequent = pvc.getSequent();
        pvc.getSymbolTable().getAllSymbols().forEach(System.out::println);;
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

        assertEquals(Result.UNSAT, z3.solve(formulae));
    }


}
