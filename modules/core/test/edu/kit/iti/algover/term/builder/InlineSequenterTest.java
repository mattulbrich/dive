/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.term.builder;

import static org.junit.Assert.assertEquals;

import java.io.InputStream;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.junit.Ignore;
import org.junit.Test;

import edu.kit.iti.algover.dafnystructures.DafnyMethod;
import edu.kit.iti.algover.parser.DafnyException;
import edu.kit.iti.algover.parser.DafnyTree;
import edu.kit.iti.algover.parser.ParserTest;
import edu.kit.iti.algover.parser.ReferenceResolutionVisitor;
import edu.kit.iti.algover.parser.TypeResolution;
import edu.kit.iti.algover.project.Project;
import edu.kit.iti.algover.proof.PVC;
import edu.kit.iti.algover.rules.TermSelector;
import edu.kit.iti.algover.symbex.Symbex;
import edu.kit.iti.algover.symbex.SymbexPath;
import edu.kit.iti.algover.term.Sequent;
import edu.kit.iti.algover.util.TestUtil;

public class InlineSequenterTest extends SequenterTest {

    protected String expectedSuccedent(String string) {
        return "$gt(p, 0)";
    }

    protected String expectedAntecedent(String string) {
        return "$gt(p, 0)";
    }

    @Override
    protected PVCSequenter makeSequenter() {
        return new InlineSequenter();
    }

    @Test
    public void testReferenceMap() throws Exception {
        InputStream is = getClass().getResourceAsStream("referencesTest.dfy");
        DafnyTree top = ParserTest.parseFile(is, null);
        // SyntacticSugarVistor.visit(top);
        Project p = TestUtil.mockProject(top);
        Symbex symbex = new Symbex();
        DafnyMethod method = p.getMethod("m");
        List<SymbexPath> results = symbex.symbolicExecution(method.getRepresentation());
        assertEquals(3, results.size());

        PVCSequenter sequenter = makeSequenter();
        SymbexPath path = results.get(0);
        Map<TermSelector, DafnyTree> map = new HashMap<>();
        Sequent sequent = sequenter.translate(path, makeTable(method), map);

        System.out.println(sequent);
        System.out.println(map);

    }

    @Test
    public void testAnonymisationProblem() throws Exception {
        InputStream is = getClass().getResourceAsStream("anonymisationProblem.dfy");
        DafnyTree top = ParserTest.parseFile(is, null);
        Project p = TestUtil.mockProject(top);

        PVC pvc = p.getPVCByName("M/loop/else/Inv[I]");
        SymbexPath path = pvc.getPathThroughProgram();

        PVCSequenter sequenter = makeSequenter();
        Map<TermSelector, DafnyTree> map = new HashMap<>();
        DafnyMethod method = (DafnyMethod) pvc.getDeclaration();
        Sequent sequent = sequenter.translate(path, makeTable(method), map);

        assertEquals("$le(i_1, n), $lt(i_1, n), $not($eq<int>(i_1, 5)) |- $le($plus(i_1, 1), n)", sequent.toString());

    }
}
