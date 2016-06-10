/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2016 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.symbex;

import static org.junit.Assert.*;

import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.InputStream;
import java.util.ArrayList;
import java.util.Deque;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;

import org.antlr.runtime.CommonToken;
import org.antlr.runtime.RecognitionException;
import org.junit.Before;
import org.junit.Test;

import edu.kit.iti.algover.parser.ParserTest;
import edu.kit.iti.algover.parser.DafnyParser;
import edu.kit.iti.algover.parser.DafnyTree;
import edu.kit.iti.algover.symbex.SymbexPath.AssertionType;
import edu.kit.iti.algover.util.ImmutableList;
import edu.kit.iti.algover.util.Pair;
import edu.kit.iti.algover.symbex.PathConditionElement.AssumptionType;

public class SymbexTest {

    private static final VariableMap SOME_MAP =
            VariableMap.EMPTY.assign("var", new DafnyTree(new CommonToken(-4)));

    private DafnyTree tree;

    private static final DafnyTree SOME_PROGRAM =
            new DafnyTree(new CommonToken(-1, "SOME_PROGRAM"));

    @Before
    public void loadTree() throws Exception {
        InputStream stream = getClass().getResourceAsStream("symbex");
        this.tree = ParserTest.parseFile(stream);
    }

    @Test
    public void testSymbolicExecution() throws Exception {

        Symbex symbex = new Symbex();
        List<SymbexPath> results = symbex.symbolicExecution(tree);

        System.out.println(results);

        assertEquals(7, results.size());

        assertEquals(AssertionType.INVARIANT_INITIALLY_VALID, results.get(0).getProofObligationType());
        assertEquals(AssertionType.INVARIANT_PRESERVED, results.get(1).getProofObligationType());
        assertEquals(AssertionType.EXPLICIT_ASSERT, results.get(2).getProofObligationType());
        assertEquals(AssertionType.POST, results.get(3).getProofObligationType());
        assertEquals(AssertionType.POST, results.get(4).getProofObligationType());
        // else branch is now there!
        assertEquals(AssertionType.POST, results.get(5).getProofObligationType());
        assertEquals(AssertionType.POST, results.get(6).getProofObligationType());
    }

    @Test
    public void testHandleAssert() {

        DafnyTree assertionStm = tree.getLastChild().getChild(6);
        assertEquals(DafnyParser.ASSERT, assertionStm.getType());

        Symbex symbex = new Symbex();
        Deque<SymbexPath> stack = new LinkedList<SymbexPath>();
        SymbexPath state = new SymbexPath(tree);
        state.setMap(SOME_MAP);
        symbex.handleAssert(stack , state, assertionStm, SOME_PROGRAM);

        assertEquals(2, stack.size());

        SymbexPath next = stack.removeLast();
        assertTrue(next.getBlockToExecute() == SOME_PROGRAM);
        assertTrue(next.getMap() == SOME_MAP);
        assertEquals(0, next.getPathConditions().size());

        SymbexPath check = stack.pop();
        assertEquals(AssertionType.EXPLICIT_ASSERT, check.getProofObligationType());
        assertEquals(1, check.getProofObligations().size());
        assertEquals("(assert (== unmodifiedInLoop 0))",
                check.getProofObligations().iterator().next().toStringTree());
    }

    @Test
    public void testHandleAssignment() {
        DafnyTree assStm = tree.getLastChild().getChild(2);
        assertEquals(DafnyParser.ASSIGN, assStm.getType());

        Symbex symbex = new Symbex();
        Deque<SymbexPath> stack = new LinkedList<SymbexPath>();
        List<SymbexPath> results = new ArrayList<SymbexPath>();
        SymbexPath state = new SymbexPath(tree);
        state.setMap(SOME_MAP);

        symbex.handleAssign(stack, state, assStm, SOME_PROGRAM);

        assertEquals(1, stack.size());
        assertEquals(0, results.size());

        SymbexPath next = stack.pop();
        assertTrue(next.getBlockToExecute() == SOME_PROGRAM);
        assertEquals("1", next.getMap().get("count").toStringTree());
        assertEquals(0, next.getPathConditions().size());
    }

    @Test
    public void testHandleVarDecl1() {
        DafnyTree decl = tree.getLastChild().getChild(0);
        assertEquals(DafnyParser.VAR, decl.getType());

        Symbex symbex = new Symbex();
        Deque<SymbexPath> stack = new LinkedList<SymbexPath>();
        List<SymbexPath> results = new ArrayList<SymbexPath>();
        SymbexPath state = new SymbexPath(tree);
        state.setMap(SOME_MAP);

        symbex.handleVarDecl(stack, state, decl, SOME_PROGRAM);

        assertEquals(1, stack.size());
        assertEquals(0, results.size());

        SymbexPath next = stack.pop();
        assertTrue(next.getBlockToExecute() == SOME_PROGRAM);
        assertEquals(SOME_MAP, next.getMap());
        assertEquals(0, next.getPathConditions().size());
    }

    // revealed a bug
    @Test
    public void testHandleVarDecl2() {
        DafnyTree decl = tree.getLastChild().getChild(9);
        assertEquals(DafnyParser.VAR, decl.getType());

        Symbex symbex = new Symbex();
        Deque<SymbexPath> stack = new LinkedList<SymbexPath>();
        List<SymbexPath> results = new ArrayList<SymbexPath>();
        SymbexPath state = new SymbexPath(tree);
        state.setMap(SOME_MAP);

        symbex.handleVarDecl(stack, state, decl, SOME_PROGRAM);

        assertEquals(1, stack.size());
        assertEquals(0, results.size());

        SymbexPath next = stack.pop();
        assertTrue(next.getBlockToExecute() == SOME_PROGRAM);
        assertEquals("42", next.getMap().get("init_direct").toStringTree());
        assertEquals(0, next.getPathConditions().size());
    }

    @Test
    public void testHandleWhile() {
        DafnyTree whileStm = tree.getLastChild().getChild(4);
        assertEquals(DafnyParser.WHILE,  whileStm.getType());

        Symbex symbex = new Symbex();
        LinkedList<SymbexPath> stack = new LinkedList<SymbexPath>();
        SymbexPath state = new SymbexPath(tree);
        state.setProofObligations(tree.getChild(3).getLastChild(), AssertionType.POST);
        state.setMap(SOME_MAP);

        symbex.handleWhile(stack, state, whileStm, SOME_PROGRAM);

        assertEquals(3, stack.size());

        {
            SymbexPath init = stack.get(0);
            assertEquals(AssertionType.INVARIANT_INITIALLY_VALID, init.getProofObligationType());
            assertEquals(0, init.getPathConditions().size());
            assertEquals(1, init.getProofObligations().size());
            assertEquals("(invariant (== p 2))", init.getProofObligations().get(0).toStringTree());
        }

        {
            SymbexPath pres = stack.get(1);
            {
                assertEquals(2, pres.getPathConditions().size());
                ImmutableList<PathConditionElement> pcs = pres.getPathConditions();
                {
                    PathConditionElement pc2 = pcs.get(0);
                    assertEquals(AssumptionType.ASSUMED_INVARIANT, pc2.getType());
                    assertEquals("(== p 2)", pc2.getExpression().toStringTree());
                }
                {
                    PathConditionElement pc1 = pcs.get(1);
                    assertEquals(AssumptionType.WHILE_TRUE, pc1.getType());
                    assertEquals("(> p 1)", pc1.getExpression().toStringTree());
                }
                {
                    assertEquals(AssertionType.INVARIANT_PRESERVED, pres.getProofObligationType());
                    assertEquals(1, pres.getProofObligations().size());
                    DafnyTree po = pres.getProofObligations().iterator().next();
                    assertEquals("(invariant (== p 2))", po.toStringTree());
                }
            }
        }
        {
            SymbexPath cont = stack.get(2);
            assertEquals(AssertionType.POST, cont.getProofObligationType());
            assertEquals(2, cont.getPathConditions().size());
            ImmutableList<PathConditionElement> pcs = cont.getPathConditions();
            {
                PathConditionElement pc1 = pcs.get(1);
                assertEquals(AssumptionType.WHILE_FALSE, pc1.getType());
                assertEquals("(not (> p 1))", pc1.getExpression().toStringTree());
            }
            {
                PathConditionElement pc2 = pcs.get(0);
                assertEquals(AssumptionType.ASSUMED_INVARIANT, pc2.getType());
                assertEquals("(== p 2)", pc2.getExpression().toStringTree());
            }
            {
                assertEquals(AssertionType.POST, cont.getProofObligationType());
                assertEquals(1, cont.getProofObligations().size());
                DafnyTree po = cont.getProofObligations().iterator().next();
                assertEquals("(> p 0)", po.toStringTree());
            }
        }
    }

//  revealed a bug
    @Test
    public void testHandleWhileAnonymisation() throws Exception {
        InputStream stream = getClass().getResourceAsStream("whileWithAnon");
        this.tree = ParserTest.parseFile(stream);

        Symbex symbex = new Symbex();
        List<SymbexPath> results = symbex.symbolicExecution(tree);

        assertEquals(3, results.size());
        {
            SymbexPath ss = results.get(0);
            assertEquals(AssertionType.INVARIANT_INITIALLY_VALID, ss.getProofObligationType());
            List<Pair<String, DafnyTree>> list = ss.getMap().toList();
            assertEquals(3, list.size());
            assertEquals("<mod, HAVOC>", list.get(0).toString());
            assertEquals("(HAVOC mod mod#1)", list.get(0).snd.toStringTree());
            assertEquals("<mod, unmod>", list.get(1).toString());
            assertEquals("<unmod, 1>", list.get(2).toString());
        }
        {
            SymbexPath ss = results.get(1);
            assertEquals(AssertionType.INVARIANT_PRESERVED, ss.getProofObligationType());
            List<Pair<String, DafnyTree>> list = ss.getMap().toList();;
            assertEquals(5, list.size());
            assertEquals("<mod, +>", list.get(0).toString());
            assertEquals("<mod, HAVOC>", list.get(1).toString());
            assertEquals("(HAVOC mod mod#2)", list.get(1).snd.toStringTree());
            assertEquals("<mod, HAVOC>", list.get(2).toString());
            assertEquals("<mod, unmod>", list.get(3).toString());
            assertEquals("<unmod, 1>", list.get(4).toString());
        }
        {
            SymbexPath ss = results.get(2);
            assertEquals(AssertionType.POST, ss.getProofObligationType());
            List<Pair<String, DafnyTree>> list = ss.getMap().toList();
            assertEquals(4, list.size());
            assertEquals("<mod, HAVOC>", list.get(0).toString());
            assertEquals("(HAVOC mod mod#2)", list.get(0).snd.toStringTree());
            assertEquals("<mod, HAVOC>", list.get(1).toString());
            assertEquals("<mod, unmod>", list.get(2).toString());
            assertEquals("<unmod, 1>", list.get(3).toString());
        }

    }
    @Test
    public void testHandleIf() {
        DafnyTree decl = tree.getLastChild().getChild(7);
        assertEquals(DafnyParser.IF, decl.getType());

        Symbex symbex = new Symbex();
        Deque<SymbexPath> stack = new LinkedList<SymbexPath>();
        List<SymbexPath> results = new ArrayList<SymbexPath>();
        SymbexPath state = new SymbexPath(tree);
        symbex.handleIf(stack, state, decl, SOME_PROGRAM);

        assertEquals(2, stack.size());
        assertEquals(0, results.size());

        SymbexPath next = stack.pop();
        assertEquals("(BLOCK (:= count 3) SOME_PROGRAM)", next.getBlockToExecute().toStringTree());
        assertEquals(1, next.getPathConditions().size());
        for (PathConditionElement pce : next.getPathConditions()) {
            assertEquals(PathConditionElement.AssumptionType.IF_ELSE, pce.getType());
            assertEquals("(not (> p 0))", pce.getExpression().toStringTree());
        }

        next = stack.pop();
        assertEquals("(BLOCK (:= count 2) SOME_PROGRAM)", next.getBlockToExecute().toStringTree());
        assertEquals(1, next.getPathConditions().size());
        for (PathConditionElement pce : next.getPathConditions()) {
            assertEquals(PathConditionElement.AssumptionType.IF_THEN, pce.getType());
            assertEquals("(> p 0)", pce.getExpression().toStringTree());
        }
    }

    // Revealed a bug
    @Test
    public void testHandleIfNoElse() {
        DafnyTree decl = tree.getLastChild().getChild(10);
        assertEquals(DafnyParser.IF, decl.getType());

        Symbex symbex = new Symbex();
        Deque<SymbexPath> stack = new LinkedList<SymbexPath>();
        List<SymbexPath> results = new ArrayList<SymbexPath>();
        SymbexPath state = new SymbexPath(tree);
        symbex.handleIf(stack, state, decl, SOME_PROGRAM);

        assertEquals(2, stack.size());
        assertEquals(0, results.size());

        SymbexPath next = stack.pop();
        assertEquals("SOME_PROGRAM", next.getBlockToExecute().toStringTree());
        assertEquals(1, next.getPathConditions().size());
        for (PathConditionElement pce : next.getPathConditions()) {
            assertEquals(PathConditionElement.AssumptionType.IF_ELSE, pce.getType());
            assertEquals("(not (== p count))", pce.getExpression().toStringTree());
        }

        next = stack.pop();
        assertEquals("(BLOCK (:= count (- count)) SOME_PROGRAM)", next.getBlockToExecute().toStringTree());
        assertEquals(1, next.getPathConditions().size());
        for (PathConditionElement pce : next.getPathConditions()) {
            assertEquals(PathConditionElement.AssumptionType.IF_THEN, pce.getType());
            assertEquals("(== p count)", pce.getExpression().toStringTree());
        }
    }

    @Test
    public void testHandleAssume() {
        DafnyTree decl = tree.getLastChild().getChild(8);
        assertEquals(DafnyParser.ASSUME, decl.getType());

        Symbex symbex = new Symbex();
        Deque<SymbexPath> stack = new LinkedList<SymbexPath>();
        List<SymbexPath> results = new ArrayList<SymbexPath>();
        SymbexPath state = new SymbexPath(tree);
        symbex.handleAssume(stack, state, decl, SOME_PROGRAM);

        assertEquals(1, stack.size());
        assertEquals(0, results.size());

        SymbexPath next = stack.pop();
        assertTrue(next.getBlockToExecute() == SOME_PROGRAM);
        assertEquals(1, next.getPathConditions().size());
        for (PathConditionElement pce : next.getPathConditions()) {
            assertEquals(PathConditionElement.AssumptionType.EXPLICIT_ASSUMPTION, pce.getType());
            assertEquals("(> count 0)", pce.getExpression().toStringTree());
        }
    }
}