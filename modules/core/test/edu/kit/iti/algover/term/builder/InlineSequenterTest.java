/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.term.builder;

import static org.junit.Assert.assertEquals;

import java.io.InputStream;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import edu.kit.iti.algover.data.SymbolTable;
import edu.kit.iti.algover.proof.ProofFormula;
import edu.kit.iti.algover.rules.TermSelector.SequentPolarity;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.term.parser.TermParser;
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
        return "[$gt(p, 0)]";
    }

    protected String expectedAntecedent(String string) {
        return "[$gt(p, 0)]";
    }

    @Override
    protected PVCSequenter makeSequenter() {
        return new InlineSequenter();
    }

    // Method for following test case in referencesTest.dfy:
    //   ensures r > 0
    //   i := x + 3;
    //   assume i > 0;
    //   i := i + 2;
    //   i := a[i];
    //   r := i;

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
        SymbolTable symbolTable = makeTable(method);
        Sequent sequent = sequenter.translate(path, symbolTable, map);

        String expectedSeq = "[Assumption]: $gt($plus(x, 3), 0) " +
                "|- [Assertion]: $gt($array_select<int>($heap, a, $plus($plus(x, 3), 2)), 0)";
        assertEquals(expectedSeq, sequent.toString());

        System.out.println(map);
        assertEquals("(> i 0)", map.get(new TermSelector(SequentPolarity.ANTECEDENT, 0)).toStringTree());
        assertEquals("(+ x 3)", map.get(new TermSelector(SequentPolarity.ANTECEDENT, 0, 0)).toStringTree());
        assertEquals("x", map.get(new TermSelector(SequentPolarity.ANTECEDENT, 0, 0, 0)).toStringTree());
        assertEquals("0", map.get(new TermSelector(SequentPolarity.ANTECEDENT, 0, 1)).toStringTree());

        assertEquals("(> r 0)", map.get(new TermSelector(SequentPolarity.SUCCEDENT, 0)).toStringTree());
        assertEquals("(ARRAY_ACCESS a i)", map.get(new TermSelector(SequentPolarity.SUCCEDENT, 0, 0)).toStringTree());
        assertEquals("(+ i 2)", map.get(new TermSelector(SequentPolarity.SUCCEDENT, 0, 0, 2)).toStringTree());
        assertEquals("(+ x 3)", map.get(new TermSelector(SequentPolarity.SUCCEDENT, 0, 0, 2, 0)).toStringTree());
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

        assertEquals("[Assumption]: $le(i_1, n), " +
                "[PathCond]: $lt(i_1, n), " +
                "[PathCond]: $not($eq<int>(i_1, 5)) " +
                "|- [Assertion]: $le($plus(i_1, 1), n)", sequent.toString());

    }

    protected void checkSequentWithOld(SymbolTable table, Sequent sequent) throws Exception {

        Term expected = TermParser.parse(table, "c.i@$heap[c.i := c.i+1] == c.i + 1");

        assertEquals(expected, sequent.getSuccedent().get(0).getTerm());
    }
}
