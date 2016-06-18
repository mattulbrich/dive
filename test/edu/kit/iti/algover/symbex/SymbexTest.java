/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2016 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.symbex;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

import java.io.InputStream;
import java.util.ArrayList;
import java.util.Deque;
import java.util.LinkedList;
import java.util.List;

import org.antlr.runtime.CommonToken;
import org.junit.Before;
import org.junit.Test;

import edu.kit.iti.algover.parser.DafnyParser;
import edu.kit.iti.algover.parser.DafnyTree;
import edu.kit.iti.algover.parser.ParserTest;
import edu.kit.iti.algover.symbex.AssertionElement.AssertionType;
import edu.kit.iti.algover.symbex.PathConditionElement.AssumptionType;
import edu.kit.iti.algover.util.ImmutableList;
import edu.kit.iti.algover.util.Pair;

public class SymbexTest {

    private static final VariableMap SOME_MAP =
            VariableMap.EMPTY.assign("var", new DafnyTree(new CommonToken(-4)));

    private DafnyTree tree;

    private static final DafnyTree SOME_PROGRAM =
            new DafnyTree(new CommonToken(-1, "SOME_PROGRAM"));

    @Before
    public void loadTree() throws Exception {
        InputStream stream = getClass().getResourceAsStream("symbex.dfy");
        this.tree = ParserTest.parseFile(stream);
    }

    @Test
    public void testSymbolicExecution() throws Exception {

        Symbex symbex = new Symbex();
        List<SymbexPath> results = symbex.symbolicExecution(tree);

        System.out.println(results);

        assertEquals(7, results.size());

        assertEquals(AssertionType.INVARIANT_INITIALLY_VALID, results.get(0).getCommonProofObligationType());
        assertEquals(AssertionType.INVARIANT_PRESERVED, results.get(1).getCommonProofObligationType());
        assertEquals(AssertionType.EXPLICIT_ASSERT, results.get(2).getCommonProofObligationType());
        assertEquals(AssertionType.POST, results.get(3).getCommonProofObligationType());
        assertEquals(AssertionType.POST, results.get(4).getCommonProofObligationType());
        // else branch is now there!
        assertEquals(AssertionType.POST, results.get(5).getCommonProofObligationType());
        assertEquals(AssertionType.POST, results.get(6).getCommonProofObligationType());
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
        assertEquals(1, next.getPathConditions().size());
        assertEquals("(== unmodifiedInLoop 0)",
                next.getPathConditions().get(0).getExpression().toStringTree());

        SymbexPath check = stack.pop();
        assertEquals("[EXPLICIT_ASSERT:(== unmodifiedInLoop 0)]",
                check.getProofObligations().toString());
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
        state.setProofObligation(tree.getChild(3).getLastChild(), tree.getChild(3), AssertionType.POST);
        state.setMap(SOME_MAP);

        symbex.handleWhile(stack, state, whileStm, SOME_PROGRAM);

        assertEquals(3, stack.size());

        {
            SymbexPath init = stack.get(0);
            assertEquals(AssertionType.INVARIANT_INITIALLY_VALID, init.getCommonProofObligationType());
            assertEquals(0, init.getPathConditions().size());
            assertEquals("[INVARIANT_INITIALLY_VALID:(== p 2)]", init.getProofObligations().toString());
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
                    assertEquals(AssertionType.INVARIANT_PRESERVED, pres.getCommonProofObligationType());
                    assertEquals(1, pres.getProofObligations().size());
                    AssertionElement po = pres.getProofObligations().get(0);
                    assertEquals("(invariant (== p 2))", po.getOrigin().toStringTree());
                    assertEquals("(== p 2)", po.getExpression().toStringTree());
                }
            }
        }
        {
            SymbexPath cont = stack.get(2);
            assertEquals(AssertionType.POST, cont.getCommonProofObligationType());
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
                assertEquals(AssertionType.POST, cont.getCommonProofObligationType());
                assertEquals(1, cont.getProofObligations().size());
                AssertionElement po = cont.getProofObligations().get(0);
                assertEquals("(> p 0)", po.getExpression().toStringTree());
            }
        }
    }

    // revealed a bug
    @Test
    public void testHandleWhileAnonymisation() throws Exception {
        InputStream stream = getClass().getResourceAsStream("whileWithAnon.dfy");
        this.tree = ParserTest.parseFile(stream);

        Symbex symbex = new Symbex();
        List<SymbexPath> results = symbex.symbolicExecution(tree);

        assertEquals(3, results.size());
        {
            SymbexPath ss = results.get(0);
            assertEquals(AssertionType.INVARIANT_INITIALLY_VALID, ss.getCommonProofObligationType());
            List<Pair<String, DafnyTree>> list = ss.getMap().toList();
            assertEquals(3, list.size());
            assertEquals("<mod, HAVOC>", list.get(0).toString());
            assertEquals("(HAVOC mod mod#1)", list.get(0).snd.toStringTree());
            assertEquals("<mod, unmod>", list.get(1).toString());
            assertEquals("<unmod, 1>", list.get(2).toString());
        }
        {
            SymbexPath ss = results.get(1);
            assertEquals(AssertionType.INVARIANT_PRESERVED, ss.getCommonProofObligationType());
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
            assertEquals(AssertionType.POST, ss.getCommonProofObligationType());
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

    @Test
    public void testHandleHavoc() throws Exception {
        InputStream stream = getClass().getResourceAsStream("havoc.dfy");
        this.tree = ParserTest.parseFile(stream);

        Symbex symbex = new Symbex();
        List<SymbexPath> results = symbex.symbolicExecution(tree);

        assertEquals(2, results.size());

        List<Pair<String, DafnyTree>> pc = results.get(0).getMap().toList();
        assertEquals("(HAVOC x x#2)", pc.get(0).snd.toStringTree());
        assertEquals("(HAVOC y y#1)", pc.get(1).snd.toStringTree());
        assertEquals("(HAVOC x x#1)", pc.get(2).snd.toStringTree());

        pc = results.get(1).getMap().toList();
        assertEquals("(HAVOC x x#2)", pc.get(0).snd.toStringTree());
        assertEquals("(HAVOC y y#1)", pc.get(1).snd.toStringTree());
        assertEquals("(HAVOC x x#1)", pc.get(2).snd.toStringTree());
    }

    @Test
    public void testHandleRuntimeAssertions() throws Exception {
        InputStream stream = getClass().getResourceAsStream("runtimeAssert.dfy");
        this.tree = ParserTest.parseFile(stream).getChild(0);

        Symbex symbex = new Symbex();
        List<SymbexPath> results = symbex.symbolicExecution(tree);

        assertEquals(5, results.size());

        {
            SymbexPath path = results.get(0);
            assertEquals(AssertionType.POST, path.getCommonProofObligationType());
        }
        {
            SymbexPath path = results.get(1);
            assertEquals(AssertionType.RT_IN_BOUNDS, path.getCommonProofObligationType());
            ImmutableList<AssertionElement> pos = path.getProofObligations();
            assertEquals(2, pos.size());
            assertEquals("(>= y 0)", pos.get(0).getExpression().toStringTree());
            assertEquals("(< y (Length a))", pos.get(1).getExpression().toStringTree());
            assertEquals(1, path.getPathConditions().size());
            assertEquals("(not (> y 0))", path.getPathConditions().get(0).getExpression().toStringTree());
        }
        {
            SymbexPath path = results.get(2);
            assertEquals(AssertionType.RT_NONNULL, path.getCommonProofObligationType());
            AssertionElement po = path.getProofObligations().get(0);
            assertEquals("(!= a null)", po.getExpression().toStringTree());
            assertEquals(1, path.getPathConditions().size());
            assertEquals("(not (> y 0))", path.getPathConditions().get(0).getExpression().toStringTree());
        }
        {
            SymbexPath path = results.get(3);
            assertEquals(AssertionType.RT_IN_BOUNDS, path.getCommonProofObligationType());
            ImmutableList<AssertionElement> pos = path.getProofObligations();
            assertEquals(2, pos.size());
            assertEquals("(>= y 0)", pos.get(0).getExpression().toStringTree());
            assertEquals("(< y (Length a))", pos.get(1).getExpression().toStringTree());
            assertEquals(0, path.getPathConditions().size());
        }
        {
            SymbexPath path = results.get(4);
            assertEquals(AssertionType.RT_NONNULL, path.getCommonProofObligationType());
            AssertionElement po = path.getProofObligations().get(0);
            assertEquals("(!= a null)", po.getExpression().toStringTree());
            assertEquals(0, path.getPathConditions().size());
        }
    }

    // revealed 2 bugs
    @Test
    public void testHandleRuntimeAssertionsIf() throws Exception {
        InputStream stream = getClass().getResourceAsStream("runtimeAssert.dfy");
        this.tree = ParserTest.parseFile(stream).getChild(1);

        Symbex symbex = new Symbex();
        List<SymbexPath> results = symbex.symbolicExecution(tree);

        assertEquals(4, results.size());

        {
            SymbexPath path = results.get(0);
            assertEquals(AssertionType.POST, path.getCommonProofObligationType());
        }
        {
            SymbexPath path = results.get(1);
            assertEquals(AssertionType.POST, path.getCommonProofObligationType());
        }
        {
            SymbexPath path = results.get(2);
            assertEquals(AssertionType.RT_IN_BOUNDS, path.getCommonProofObligationType());
            ImmutableList<AssertionElement> pos = path.getProofObligations();
            assertEquals(2, pos.size());
            assertEquals("(>= i 0)", pos.get(0).getExpression().toStringTree());
            assertEquals("(< i (Length a))", pos.get(1).getExpression().toStringTree());
            assertEquals(1, path.getPathConditions().size());
            assertEquals("(> i 0)", path.getPathConditions().get(0).getExpression().toStringTree());
        }
        {
            SymbexPath path = results.get(3);
            assertEquals(AssertionType.RT_NONNULL, path.getCommonProofObligationType());
            AssertionElement po = path.getProofObligations().get(0);
            assertEquals("(!= a null)", po.getExpression().toStringTree());
            assertEquals(1, path.getPathConditions().size());
            assertEquals("(> i 0)", path.getPathConditions().get(0).getExpression().toStringTree());
        }
    }

    @Test
    public void testHandleRuntimeAssertionsWhile() throws Exception {
        InputStream stream = getClass().getResourceAsStream("runtimeAssert.dfy");
        this.tree = ParserTest.parseFile(stream).getChild(2);

        Symbex symbex = new Symbex();
        List<SymbexPath> results = symbex.symbolicExecution(tree);

        assertEquals(5, results.size());

        int i=0;
        {
            SymbexPath path = results.get(i++);
            assertEquals(AssertionType.RT_IN_BOUNDS, path.getCommonProofObligationType());
            ImmutableList<AssertionElement> pos = path.getProofObligations();
            assertEquals(2, pos.size());
            assertEquals("(>= i 0)", pos.get(0).getExpression().toStringTree());
            assertEquals("(< i (Length a))", pos.get(1).getExpression().toStringTree());
            assertEquals(2, path.getPathConditions().size());
            assertEquals("(> i 2)", path.getPathConditions().get(0).getExpression().toStringTree());
            assertEquals("(> i 0)", path.getPathConditions().get(1).getExpression().toStringTree());
            assertEquals(1, path.getMap().toList().size());
        }
        {
            SymbexPath path = results.get(i++);
            assertEquals(AssertionType.RT_NONNULL, path.getCommonProofObligationType());
            AssertionElement po = path.getProofObligations().get(0);
            assertEquals("(!= a null)", po.getExpression().toStringTree());
            assertEquals(2, path.getPathConditions().size());
            assertEquals("(> i 2)", path.getPathConditions().get(0).getExpression().toStringTree());
            assertEquals("(> i 0)", path.getPathConditions().get(1).getExpression().toStringTree());
            assertEquals(1, path.getMap().toList().size());
        }
        {
            SymbexPath path = results.get(i++);
            assertEquals(AssertionType.INVARIANT_INITIALLY_VALID, path.getCommonProofObligationType());
        }
        {
            SymbexPath path = results.get(i++);
            assertEquals(AssertionType.INVARIANT_PRESERVED, path.getCommonProofObligationType());
        }
        {
            SymbexPath path = results.get(i++);
            assertEquals(AssertionType.POST, path.getCommonProofObligationType());
        }
    }
}