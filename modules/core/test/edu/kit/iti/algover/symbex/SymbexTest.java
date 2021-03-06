/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.symbex;

import edu.kit.iti.algover.dafnystructures.DafnyMethod;
import edu.kit.iti.algover.parser.DafnyException;
import edu.kit.iti.algover.parser.DafnyParser;
import edu.kit.iti.algover.parser.DafnyParserException;
import edu.kit.iti.algover.parser.DafnyTree;
import edu.kit.iti.algover.parser.ParserTest;
import edu.kit.iti.algover.parser.TypeResolutionTest;
import edu.kit.iti.algover.project.Project;
import edu.kit.iti.algover.symbex.AssertionElement.AssertionType;
import edu.kit.iti.algover.symbex.PathConditionElement.AssumptionType;
import edu.kit.iti.algover.term.builder.UpdateSequenter;
import edu.kit.iti.algover.util.ASTUtil;
import edu.kit.iti.algover.util.ImmutableList;
import edu.kit.iti.algover.util.SymbexUtil;
import edu.kit.iti.algover.util.TestUtil;
import edu.kit.iti.algover.util.Util;
import org.antlr.runtime.RecognitionException;
import org.junit.Before;
import org.junit.Test;

import java.io.IOException;
import java.io.InputStream;
import java.util.*;

import static org.junit.Assert.*;

public class SymbexTest {

    private static final ImmutableList<DafnyTree> SOME_HISTORY =
            ImmutableList.single(ASTUtil.assign(ASTUtil.id("someVar"),
                    ASTUtil.intLiteral(42)));
    private static final DafnyTree SOME_PROGRAM =
            new DafnyTree(-1, "SOME_PROGRAM");
    private DafnyTree tree;

    // @Before ... not for all test cases!
    public void loadTree() throws Exception {
        InputStream stream = getClass().getResourceAsStream("symbex.dfy");
        DafnyTree fileTree = ParserTest.parseFile(stream);

        // performs type analysis etc:
        TestUtil.mockProject(fileTree);

        this.tree = fileTree.getChild(0);
    }

    @Test
    public void testSymbolicExecution() throws Exception {

        loadTree();
        Symbex symbex = new Symbex();
        List<SymbexPath> results = symbex.symbolicExecution(tree);

        //System.out.println(results);

        assertEquals(7, results.size());

        assertEquals(AssertionType.INVARIANT_INITIALLY_VALID, results.get(0).getCommonProofObligationType());
        assertEquals(null, results.get(1).getCommonProofObligationType());
        assertEquals(AssertionType.INVARIANT_PRESERVED, results.get(1).split().get(0).getCommonProofObligationType());
        assertEquals(AssertionType.VARIANT_DECREASED, results.get(1).split().get(1).getCommonProofObligationType());
        assertEquals(AssertionType.EXPLICIT_ASSERT, results.get(2).getCommonProofObligationType());
        assertEquals(AssertionType.POST, results.get(3).getCommonProofObligationType());
        assertEquals(AssertionType.POST, results.get(4).getCommonProofObligationType());
        // else branch is now there!
        assertEquals(AssertionType.POST, results.get(5).getCommonProofObligationType());
        assertEquals(AssertionType.POST, results.get(6).getCommonProofObligationType());
    }

    @Test
    public void testHandleAssert() throws Exception {

        loadTree();
        DafnyTree assertionStm = tree.getLastChild().getChild(6);
        assertEquals(DafnyParser.ASSERT, assertionStm.getType());

        Symbex symbex = new Symbex();
        Deque<SymbexPath> stack = new LinkedList<SymbexPath>();
        SymbexPath state = new SymbexPath(tree);
        state.setAssignmentHistory(SOME_HISTORY);
        symbex.handleAssert(stack , state, assertionStm, SOME_PROGRAM);

        assertEquals(2, stack.size());

        SymbexPath next = stack.removeLast();
        assertTrue(next.getBlockToExecute() == SOME_PROGRAM);
        assertTrue(next.getAssignmentHistory() == SOME_HISTORY);
        assertEquals(1, next.getPathConditions().size());
        assertEquals("(== unmodifiedInLoop 0)",
                next.getPathConditions().get(0).getExpression().toStringTree());

        SymbexPath check = stack.pop();
        assertEquals("[EXPLICIT_ASSERT:(== unmodifiedInLoop 0)]",
                check.getProofObligations().toString());
    }

    @Test
    public void testHandleAssignment() throws Exception {
        loadTree();
        DafnyTree assStm = tree.getLastChild().getChild(2);
        assertEquals(DafnyParser.ASSIGN, assStm.getType());

        Symbex symbex = new Symbex();
        Deque<SymbexPath> stack = new LinkedList<SymbexPath>();
        List<SymbexPath> results = new ArrayList<SymbexPath>();
        SymbexPath state = new SymbexPath(tree);
        state.setAssignmentHistory(SOME_HISTORY);

        symbex.handleAssign(stack, state, assStm, SOME_PROGRAM);

        assertEquals(1, stack.size());
        assertEquals(0, results.size());

        SymbexPath next = stack.pop();
        assertTrue(next.getBlockToExecute() == SOME_PROGRAM);
        assertEquals("(:= count 1)", next.getAssignmentHistory().getHead().toStringTree());
        assertEquals(0, next.getPathConditions().size());
    }

    @Test
    public void testHandleVarDecl1() throws Exception {
        loadTree();
        DafnyTree decl = tree.getLastChild().getChild(0);
        assertEquals(DafnyParser.VAR, decl.getType());

        Symbex symbex = new Symbex();
        Deque<SymbexPath> stack = new LinkedList<SymbexPath>();
        List<SymbexPath> results = new ArrayList<SymbexPath>();
        SymbexPath state = new SymbexPath(tree);
        state.setAssignmentHistory(SOME_HISTORY);

        symbex.handleVarDecl(stack, state, decl, SOME_PROGRAM);

        assertEquals(1, stack.size());
        assertEquals(0, results.size());

        SymbexPath next = stack.pop();
        assertTrue(next.getBlockToExecute() == SOME_PROGRAM);
        assertTrue(next.getAssignmentHistory() == SOME_HISTORY);
        assertEquals(0, next.getPathConditions().size());
    }

    // revealed a bug
    @Test
    public void testHandleVarDecl2() throws Exception {
        loadTree();
        DafnyTree decl = tree.getLastChild().getChild(9);
        assertEquals(DafnyParser.VAR, decl.getType());

        Symbex symbex = new Symbex();
        Deque<SymbexPath> stack = new LinkedList<SymbexPath>();
        List<SymbexPath> results = new ArrayList<SymbexPath>();
        SymbexPath state = new SymbexPath(tree);
        state.setAssignmentHistory(SOME_HISTORY);

        symbex.handleVarDecl(stack, state, decl, SOME_PROGRAM);

        assertEquals(1, stack.size());
        assertEquals(0, results.size());

        SymbexPath next = stack.pop();
        assertSame(SOME_PROGRAM, next.getBlockToExecute());
        assertEquals("(ASSIGN init_direct 43)", next.getAssignmentHistory().getHead().toStringTree());
        assertEquals(0, next.getPathConditions().size());
    }

    // revealed a bug
    @Test
    public void testHandleVarDecl3() throws Exception {
        loadTree();
        DafnyTree decl = tree.getLastChild().getChild(10);
        assertEquals(DafnyParser.VAR, decl.getType());

        Symbex symbex = new Symbex();
        Deque<SymbexPath> stack = new LinkedList<SymbexPath>();
        List<SymbexPath> results = new ArrayList<SymbexPath>();
        SymbexPath state = new SymbexPath(tree);
        state.setAssignmentHistory(SOME_HISTORY);

        symbex.handleVarDecl(stack, state, decl, SOME_PROGRAM);

        assertEquals(1, stack.size());
        assertEquals(0, results.size());

        SymbexPath next = stack.pop();
        assertSame(SOME_PROGRAM, next.getBlockToExecute());
        assertEquals("(ASSIGN init_wo_type 41)", next.getAssignmentHistory().getHead().toStringTree());
        assertEquals(0, next.getPathConditions().size());
    }



    // bug in handlling wildcard anonymisation
    @Test
    public void testHandleWhile() throws Exception {
        loadTree();
        DafnyTree whileStm = tree.getLastChild().getChild(4);
        assertEquals(DafnyParser.WHILE,  whileStm.getType());

        Symbex symbex = new Symbex();
        LinkedList<SymbexPath> stack = new LinkedList<SymbexPath>();
        SymbexPath state = new SymbexPath(tree);
        state.setProofObligation(tree.getChild(3).getLastChild(), tree.getChild(3), AssertionType.POST);
        state.setAssignmentHistory(SOME_HISTORY);

        symbex.handleWhile(stack, state, whileStm, SOME_PROGRAM);

        assertEquals(3, stack.size());

        {
            SymbexPath init = stack.get(0);
            assertEquals(AssertionType.INVARIANT_INITIALLY_VALID, init.getCommonProofObligationType());
            assertEquals(0, init.getPathConditions().size());
            assertEquals("[INVARIANT_INITIALLY_VALID:(== p 2)]", init.getProofObligations().toString());
        }

        {
            List<SymbexPath> paths = stack.get(1).split();
            assertEquals(2, paths.size());
            {
                SymbexPath pres = paths.get(0);
                assertEquals(AssertionType.INVARIANT_PRESERVED, pres.getCommonProofObligationType());
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
                    assertEquals(1, pres.getProofObligations().size());
                    AssertionElement po = pres.getProofObligations().get(0);
                    assertEquals("(invariant (== p 2))", po.getOrigin().toStringTree());
                    assertEquals("(== p 2)", po.getExpression().toStringTree());
                }
            }
            {
                SymbexPath decr = paths.get(1);
                assertEquals(AssertionType.VARIANT_DECREASED, decr.getCommonProofObligationType());
                // has the same path conditions as above, no need to check again
                {
                    assertEquals(1, decr.getProofObligations().size());
                    AssertionElement po = decr.getProofObligations().get(0);
                    assertEquals("(decreases (+ p count))", po.getOrigin().toStringTree());
                    assertEquals("(NOETHER_LESS (LISTEX (+ p count)) (LISTEX $decr_1))", po.getExpression().toStringTree());
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

    // revealed a bug, and another
    // and another months later ...
    @Test
    public void testHandleWhileAnonymisation() throws Exception {
        InputStream stream = getClass().getResourceAsStream("whileWithAnon.dfy");
        DafnyTree parseTree = ParserTest.parseFile(stream);
        TestUtil.mockProject(parseTree);
        this.tree = parseTree
                .getFirstChildWithType(DafnyParser.CLASS)
                .getFirstChildWithType(DafnyParser.METHOD);

        Symbex symbex = new Symbex();
        List<SymbexPath> results = symbex.symbolicExecution(tree);

        assertEquals(5, results.size());
        {
            SymbexPath ss = results.get(0);
            assertEquals(AssertionType.INVARIANT_INITIALLY_VALID, ss.getCommonProofObligationType());
            ImmutableList<DafnyTree> list = ss.getAssignmentHistory();
            assertEquals("[(ASSIGN $mod (+ modset (CALL $freshObjects (ARGS $heap)))), (ASSIGN $decr 0), (ASSIGN $oldheap $heap), (:= unmod 1), (:= mod unmod), (:= mod (+ mod 2))]",
                    list.map(x -> x.toStringTree()).toString());
        }
        {
            List<SymbexPath> ss = results.get(1).split();
            {
                SymbexPath pres = ss.get(0);
                assertEquals(AssertionType.INVARIANT_PRESERVED, pres.getCommonProofObligationType());
                ImmutableList<DafnyTree> list = pres.getAssignmentHistory();
                assertEquals("[(ASSIGN $mod (+ modset[set<C>] (CALL $freshObjects (ARGS $heap)))), "
                                + "(ASSIGN $decr 0), "
                                + "(ASSIGN $oldheap $heap), "
                                + "(:= unmod[int] 1[int]), (:= mod[int] unmod[int]), "
                                + "(:= mod[int] (+ mod[int] 2[int])[int]), "
                                + "(ASSIGN mod[int] WILDCARD[int]), "
                                + "(ASSIGN $heap (CALL $anon (ARGS $heap $mod $aheap_1))), "
                                + "(ASSIGN $decr_1 (+ unmod[int] mod[int])[int]), "
                                + "(:= mod[int] (+ mod[int] 1[int])[int]), "
                                + "(:= field[int] 1[int])]",
                        list.map(x -> TypeResolutionTest.toTypedString(x)).toString());


            }
            {
                SymbexPath decr = ss.get(1);
                assertEquals(AssertionType.VARIANT_DECREASED, decr.getCommonProofObligationType());
            }
        }
        {
            SymbexPath ss = results.get(4);
            assertEquals(AssertionType.POST, ss.getCommonProofObligationType());
            ImmutableList<DafnyTree> list = ss.getAssignmentHistory();
            assertEquals("[(ASSIGN $mod (+ modset (CALL $freshObjects (ARGS $heap)))), "
                            + "(ASSIGN $decr 0), "
                            + "(ASSIGN $oldheap $heap), "
                            + "(:= unmod 1), (:= mod unmod), (:= mod (+ mod 2)), "
                            + "(ASSIGN mod WILDCARD), "
                            + "(ASSIGN $heap (CALL $anon (ARGS $heap $mod $aheap_1)))]",
                    list.map(x -> x.toStringTree()).toString());
        }

    }
    @Test
    public void testHandleIf() throws Exception {
        loadTree();
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
    public void testHandleIfNoElse() throws Exception {
        loadTree();

        DafnyTree decl = tree.getLastChild().getChild(11);
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
    public void testHandleAssume() throws Exception {
        loadTree();

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
        Project project = TestUtil.mockProject(ParserTest.parseFile(stream));
        this.tree = project.getMethod("havocTest").getRepresentation();

        Symbex symbex = new Symbex();
        List<SymbexPath> results = symbex.symbolicExecution(tree);

        assertEquals(2, results.size());

        ImmutableList<DafnyTree> pc = results.get(0).getAssignmentHistory();
        assertEquals("[(ASSIGN $mod (CALL $freshObjects (ARGS $heap))), (ASSIGN $decr 0), (ASSIGN $oldheap $heap), (:= x *), (:= y *), (:= x *)]", pc.map(x -> x.toStringTree()).toString());

        pc = results.get(1).getAssignmentHistory();
        assertEquals("[(ASSIGN $mod (CALL $freshObjects (ARGS $heap))), (ASSIGN $decr 0), (ASSIGN $oldheap $heap), (:= x *), (:= y *), (:= x *)]", pc.map(x -> x.toStringTree()).toString());
    }

    @Test
    public void testHandleRuntimeAssertions() throws Exception {
        InputStream stream = getClass().getResourceAsStream("runtimeAssert.dfy");
        Project project = TestUtil.mockProject(ParserTest.parseFile(stream));
        this.tree = project.getMethod("runtimeChecks").getRepresentation();

        Symbex symbex = new Symbex();
        List<SymbexPath> results = symbex.symbolicExecution(tree);

        int cnt = 0;
        {
            SymbexPath path = results.get(cnt++);
            assertEquals(AssertionType.POST, path.getCommonProofObligationType());
        }
        //  x := a[y] + a2.Length;
        {
            SymbexPath path = results.get(cnt++);
            assertEquals(AssertionType.RT_NONNULL, path.getCommonProofObligationType());
            AssertionElement po = path.getProofObligations().get(0);
            assertEquals("(!= a null)", po.getExpression().toStringTree());
            assertEquals(0, path.getPathConditions().size());
        }
        {
            SymbexPath path = results.get(cnt++);
            assertEquals(AssertionType.RT_IN_BOUNDS, path.getCommonProofObligationType());
            ImmutableList<AssertionElement> pos = path.getProofObligations();
            assertEquals("[(&& (<= 0 y) (< y (Length a)))]",
                    pos.map(x->x.getExpression().toStringTree()).toString());
            assertEquals(0, path.getPathConditions().size());
        }
        {
            SymbexPath path = results.get(cnt++);
            assertEquals(AssertionType.RT_NONNULL, path.getCommonProofObligationType());
            AssertionElement po = path.getProofObligations().get(0);
            assertEquals("(!= a2 null)", po.getExpression().toStringTree());
            assertEquals(0, path.getPathConditions().size());
        }

        // b := y > 0 || a[y] > 0;
        {
            SymbexPath path = results.get(cnt++);
            assertEquals(AssertionType.RT_NONNULL, path.getCommonProofObligationType());
            AssertionElement po = path.getProofObligations().get(0);
            assertEquals("(==> (not (> y 0)) (!= a null))", po.getExpression().toStringTree());
            assertEquals(0, path.getPathConditions().size());
        }
        {
            SymbexPath path = results.get(cnt++);
            assertEquals(AssertionType.RT_IN_BOUNDS, path.getCommonProofObligationType());
            ImmutableList<AssertionElement> pos = path.getProofObligations();
            assertEquals("[(==> (not (> y 0)) (&& (<= 0 y) (< y (Length a))))]",
                    pos.map(x->x.getExpression().toStringTree()).toString());
            assertEquals(0, path.getPathConditions().size());
        }

        // b := multiDim[x,y] > 0;
         {
            SymbexPath path = results.get(cnt++);
            assertEquals(AssertionType.RT_NONNULL, path.getCommonProofObligationType());
            AssertionElement po = path.getProofObligations().get(0);
            assertEquals("(!= multiDim null)", po.getExpression().toStringTree());
            assertEquals(0, path.getPathConditions().size());
        }
        {
            SymbexPath path = results.get(cnt++);
            assertEquals(AssertionType.RT_IN_BOUNDS, path.getCommonProofObligationType());
            ImmutableList<AssertionElement> pos = path.getProofObligations();
            assertEquals(1, pos.size());
            assertEquals("(&& (<= 0 x) (< x (Length0 multiDim)))",
                    pos.get(0).getExpression().toStringTree());
            assertEquals(0, path.getPathConditions().size());
        }
        {
            SymbexPath path = results.get(cnt++);
            assertEquals(AssertionType.RT_IN_BOUNDS, path.getCommonProofObligationType());
            ImmutableList<AssertionElement> pos = path.getProofObligations();
            assertEquals(1, pos.size());
            assertEquals("(&& (<= 0 y) (< y (Length1 multiDim)))",
                    pos.get(0).getExpression().toStringTree());
            assertEquals(0, path.getPathConditions().size());
        }

        // y := x/y;
        {
            SymbexPath path = results.get(cnt++);
            assertEquals(AssertionType.RT_DIV0, path.getCommonProofObligationType());
            ImmutableList<AssertionElement> pos = path.getProofObligations();
            assertEquals(1, pos.size());
            assertEquals("(!= y 0)", pos.get(0).getExpression().toStringTree());
            assertEquals(0, path.getPathConditions().size());
        }
    }

    // revealed 2 bugs
    //   if(i>0 && 5+a[i] > 0)
    //   {} else {}
    @Test
    public void testHandleRuntimeAssertionsIf() throws Exception {
        InputStream stream = getClass().getResourceAsStream("runtimeAssert.dfy");
        Project project = TestUtil.mockProject(ParserTest.parseFile(stream));
        this.tree = project.getMethod("runtimeInIf").getRepresentation();

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
            assertEquals(AssertionType.RT_NONNULL, path.getCommonProofObligationType());
            AssertionElement po = path.getProofObligations().get(0);
            assertEquals("(==> (> i 0) (!= a null))", po.getExpression().toStringTree());
            assertEquals(0, path.getPathConditions().size());
        }
        {
            SymbexPath path = results.get(3);
            assertEquals(AssertionType.RT_IN_BOUNDS, path.getCommonProofObligationType());
            ImmutableList<AssertionElement> pos = path.getProofObligations();
            assertEquals(1, pos.size());
            assertEquals("(==> (> i 0) (&& (<= 0 i) (< i (Length a))))",
                    pos.get(0).getExpression().toStringTree());
            assertEquals(0, path.getPathConditions().size());
        }

    }

    // revealed a bug
    //  while(i>0 ==> a[i]-i > 0)
    //     invariant i>2
    //     decreases i
    //   { i := i + 1; }
    @Test
    public void testHandleRuntimeAssertionsWhile() throws Exception {
        InputStream stream = getClass().getResourceAsStream("runtimeAssert.dfy");
        DafnyTree parseTree = ParserTest.parseFile(stream);
        Project project = TestUtil.mockProject(parseTree);
        this.tree = project.getMethod("runtimeInWhile").getRepresentation();

        Symbex symbex = new Symbex();
        List<SymbexPath> results = symbex.symbolicExecution(tree);

        assertEquals(5, results.size());

        int i=0;
        {
            SymbexPath path = results.get(i++);
            assertEquals(AssertionType.INVARIANT_INITIALLY_VALID, path.getCommonProofObligationType());
        }
        {
            SymbexPath path = results.get(i++);
            assertEquals(AssertionType.RT_NONNULL, path.getCommonProofObligationType());
            AssertionElement po = path.getProofObligations().get(0);
            assertEquals("(==> (> i 0) (!= a null))", po.getExpression().toStringTree());
            assertEquals(1, path.getPathConditions().size());
            assertEquals("(> i 2)", path.getPathConditions().get(0).getExpression().toStringTree());
            assertEquals("[(ASSIGN $mod (CALL $freshObjects (ARGS $heap))), "
                            + "(ASSIGN $decr 0), "
                            + "(ASSIGN $oldheap $heap), "
                            + "(ASSIGN i WILDCARD), "
                            + "(ASSIGN $decr_1 i)]",
                    path.getAssignmentHistory().map(x->x.toStringTree()).toString());
        }
        {
            SymbexPath path = results.get(i++);
            assertEquals(AssertionType.RT_IN_BOUNDS, path.getCommonProofObligationType());
            ImmutableList<AssertionElement> pos = path.getProofObligations();
            assertEquals(1, pos.size());
            assertEquals("(==> (> i 0) (&& (<= 0 i) (< i (Length a))))",
                    pos.get(0).getExpression().toStringTree());
            assertEquals(1, path.getPathConditions().size());
            assertEquals("(> i 2)", path.getPathConditions().get(0).getExpression().toStringTree());
            assertEquals("[(ASSIGN $mod (CALL $freshObjects (ARGS $heap))), "
                            + "(ASSIGN $decr 0), "
                            + "(ASSIGN $oldheap $heap), "
                            + "(ASSIGN i WILDCARD), "
                            + "(ASSIGN $decr_1 i)]",
                    path.getAssignmentHistory().map(x->x.toStringTree()).toString());
        }
        {
            List<SymbexPath> paths = results.get(i++).split();
            assertEquals(AssertionType.INVARIANT_PRESERVED, paths.get(0).getCommonProofObligationType());
            assertEquals(AssertionType.VARIANT_DECREASED, paths.get(1).getCommonProofObligationType());
        }
        {
            SymbexPath path = results.get(i++);
            assertEquals(AssertionType.POST, path.getCommonProofObligationType());
        }
    }

    // discovered missing in-depth analysis for RT checks
    // and in modifies analysis
    @Test
    public void testHandleHeapUpdates() throws Exception {
        InputStream stream = getClass().getResourceAsStream("../parser/reftypes.dfy");
        Project project = TestUtil.mockProject(ParserTest.parseFile(stream));

        this.tree = project.getClass("LinkedList").getMethod("m").getRepresentation();

        Symbex symbex = new Symbex();
        List<SymbexPath> results = symbex.symbolicExecution(tree);
        Collections.reverse(results);

        // results.forEach(x->System.out.println(SymbexUtil.toString(x)));

        assertEquals(15, results.size());

        // The order changed after some time ...
        int i = 0;
        i=9;
        assertEquals(AssertionType.RT_NONNULL, results.get(i).getCommonProofObligationType());
        assertEquals("[(!= z null)]", results.get(i).getProofObligations().map(x -> x.getExpression().toStringTree()).toString());

        i++;
        i=8;
        assertEquals(AssertionType.RT_NONNULL, results.get(i).getCommonProofObligationType());
        assertEquals("[(!= x null)]", results.get(i).getProofObligations().map(x -> x.getExpression().toStringTree()).toString());

        i++;
        i=10;
        assertEquals(AssertionType.MODIFIES, results.get(i).getCommonProofObligationType());
        assertEquals("[(IN x $mod)]", results.get(i).getProofObligations().map(x -> x.getExpression().toStringTree()).toString());

        i++;
        i=7;
        assertEquals(AssertionType.RT_NONNULL, results.get(i).getCommonProofObligationType());
        assertEquals("[(!= z null)]", results.get(i).getProofObligations().map(x -> x.getExpression().toStringTree()).toString());

        i++;
        i=11;
        assertEquals(AssertionType.MODIFIES, results.get(i).getCommonProofObligationType());
        assertEquals("[(IN z $mod)]", results.get(i).getProofObligations().map(x -> x.getExpression().toStringTree()).toString());

        i++;
        i=6;
        assertEquals(AssertionType.RT_NONNULL, results.get(i).getCommonProofObligationType());
        assertEquals("[(!= (FIELD_ACCESS x next) null)]", results.get(i).getProofObligations().map(x -> x.getExpression().toStringTree()).toString());

        i++;
        i=5;
        assertEquals(AssertionType.RT_NONNULL, results.get(i).getCommonProofObligationType());
        assertEquals("[(!= x null)]", results.get(i).getProofObligations().map(x -> x.getExpression().toStringTree()).toString());

        i++;
        i=12;
        assertEquals(AssertionType.MODIFIES, results.get(i).getCommonProofObligationType());
        assertEquals("[(IN (FIELD_ACCESS x next) $mod)]", results.get(i).getProofObligations().map(x -> x.getExpression().toStringTree()).toString());

        i++;
        i=4;
        assertEquals(AssertionType.RT_NONNULL, results.get(i).getCommonProofObligationType());
        assertEquals("[(!= (FIELD_ACCESS this prev) null)]", results.get(i).getProofObligations().map(x -> x.getExpression().toStringTree()).toString());

        i++;
        i=3;
        assertEquals(AssertionType.RT_NONNULL, results.get(i).getCommonProofObligationType());
        assertEquals("[(!= a null)]", results.get(i).getProofObligations().map(x -> x.getExpression().toStringTree()).toString());

        i++;
        i=2;
        assertEquals(AssertionType.RT_IN_BOUNDS, results.get(i).getCommonProofObligationType());
        assertEquals("[(&& (<= 0 0) (< 0 (Length a)))]", results.get(i).getProofObligations().map(x -> x.getExpression().toStringTree()).toString());

        i++;
        i=13;
        assertEquals(AssertionType.MODIFIES, results.get(i).getCommonProofObligationType());
        assertEquals("[(IN a $mod)]", results.get(i).getProofObligations().map(x -> x.getExpression().toStringTree()).toString());

        i++;
        i=1;
        assertEquals(AssertionType.RT_NONNULL, results.get(i).getCommonProofObligationType());
        assertEquals("[(!= a null)]", results.get(i).getProofObligations().map(x -> x.getExpression().toStringTree()).toString());

        i++;
        i=0;
        assertEquals(AssertionType.RT_IN_BOUNDS, results.get(i).getCommonProofObligationType());
        assertEquals("[(&& (<= 0 1) (< 1 (Length a)))]", results.get(i).getProofObligations().map(x -> x.getExpression().toStringTree()).toString());

        i++;
        i=14;
        assertEquals(AssertionType.POST, results.get(i).getCommonProofObligationType());
        assertEquals("[(== 1 1)]", results.get(i).getProofObligations().map(x -> x.getExpression().toStringTree()).toString());

        assertEquals(14, i);

        assertEquals("[(ASSIGN $mod (CALL $freshObjects (ARGS $heap))), "
                + "(ASSIGN $decr 0), "
                + "(ASSIGN $oldheap $heap), "
                + "(:= z next), "
                + "(:= next z), "
                + "(:= z (FIELD_ACCESS this next)), "
                + "(:= (FIELD_ACCESS this next) z), "
                + "(:= z (FIELD_ACCESS z next)), "
                + "(:= (FIELD_ACCESS x next) z), "
                + "(:= (FIELD_ACCESS z next) (FIELD_ACCESS this prev)), "
                + "(:= (FIELD_ACCESS (FIELD_ACCESS x next) next) (FIELD_ACCESS (FIELD_ACCESS this prev) prev)), "
                + "(:= (ARRAY_ACCESS a 0) (ARRAY_ACCESS a 1)), "
                + "(:= y z)]",
                results.get(i).getAssignmentHistory().map(x->x.toStringTree()).toString());

    }

    @Test
    public void testFromSymbex() throws Exception {

        InputStream stream = getClass().getResourceAsStream("noetherTest.dfy");
        DafnyTree fileTree = ParserTest.parseFile(stream);

        // performs type analysis etc:
        TestUtil.mockProject(fileTree);

        DafnyTree tree = fileTree.getChild(0);
        Symbex symbex = new Symbex();
        List<SymbexPath> results = symbex.symbolicExecution(tree);

        System.out.println(results);

        assertEquals(4, results.size());

        // preserves are interesting. Focus on of the two here
        {
            SymbexPath path = results.get(2);
            List<String> localVars = Util.map(path.getDeclaredLocalVars(), x -> x.getName());
            assertTrue(localVars.contains("$decr_1"));
            assertTrue(Util.map(path.getDeclaredLocalVars(), x -> x.getName()).contains("$decr_2"));
            assertFalse(Util.map(path.getDeclaredLocalVars(), x -> x.getName()).contains("$decr_3"));

            List<String> assignments = Util.map(path.getAssignmentHistory(), x -> x.toStringTree());
            assertTrue(assignments.contains("(ASSIGN $decr_1 y)"));
            assertTrue(assignments.contains("(ASSIGN $decr_2 x)"));

            assertEquals(1, path.getProofObligations().size());
            AssertionElement proofObl = path.getProofObligations().getHead();
            assertEquals(AssertionType.VARIANT_DECREASED, proofObl.getType());
            assertEquals("(NOETHER_LESS (LISTEX y x) (LISTEX $decr_1 $decr_2))",
                    proofObl.getExpression().toStringTree());
        }
    }

    @Test
    public void testMethodCalls() throws Exception {
        InputStream stream = getClass().getResourceAsStream("methodCalls.dfy");
        DafnyTree fileTree = ParserTest.parseFile(stream);

        // performs type analysis etc:
        Project project = TestUtil.mockProject(fileTree);

        DafnyTree tree = project.getMethod("test").getRepresentation();
        Symbex symbex = new Symbex();
        List<SymbexPath> results = symbex.symbolicExecution(tree);

        int index = 0;
        {
            SymbexPath path = results.get(index++);
            assertEquals("EstPre[CallMe]", path.getPathIdentifier());
            assertEquals(0, path.getPathConditions().size());
            assertEquals("[(ASSIGN $mod (CALL $freshObjects (ARGS $heap))), (ASSIGN $decr 0), (ASSIGN $oldheap $heap)]", path.getAssignmentHistory().map(DafnyTree::toStringTree).toString());
            assertEquals("[(LET (VAR r p) $res_CallMe_1 22 (== p 1))]",
                    path.getProofObligations().map(x -> x.getExpression().toStringTree()).toString());
        }
        {
            SymbexPath path = results.get(index++);
            assertEquals("EstPre[CallMe]", path.getPathIdentifier());
            assertEquals(1, path.getPathConditions().size());
            assertEquals("(LET (VAR r p) $res_CallMe_1 22 (== r 2))",
                    path.getPathConditions().getLast().getExpression().toStringTree());
            assertEquals("[(ASSIGN $mod (CALL $freshObjects (ARGS $heap))), (ASSIGN $decr 0), (ASSIGN $oldheap $heap), (ASSIGN x $res_CallMe_1)]",
                    path.getAssignmentHistory().map(DafnyTree::toStringTree).toString());
            assertEquals("[(LET (VAR r p) $res_CallMe_2 23 (== p 1))]",
                    path.getProofObligations().map(x -> x.getExpression().toStringTree()).toString());
        }
        {
            SymbexPath path = results.get(index++);
            assertEquals("EstPre[Meth]", path.getPathIdentifier());
            assertEquals(2, path.getPathConditions().size());
            assertEquals("(LET (VAR r p) $res_CallMe_2 23 (== r 2))",
                    path.getPathConditions().getLast().getExpression().toStringTree());
            assertEquals("[(ASSIGN $mod (CALL $freshObjects (ARGS $heap))), (ASSIGN $decr 0), (ASSIGN $oldheap $heap), (ASSIGN x $res_CallMe_1), (ASSIGN y $res_CallMe_2)]",
                    path.getAssignmentHistory().map(DafnyTree::toStringTree).toString());
            assertEquals("[(LET (VAR this p) c 24 (== p 21))]",
                    path.getProofObligations().map(x -> x.getExpression().toStringTree()).toString());
        }
        {
            SymbexPath path = results.get(index++);
            assertEquals("Modifies[Meth]", path.getPathIdentifier());
            assertEquals(2, path.getPathConditions().size());
            // not rechecking the last stuff...
            assertEquals("[(LE (LET (VAR this p) c 24 (SETEX this)) $mod)]",
                    path.getProofObligations().map(x -> x.getExpression().toStringTree()).toString());
        }
        {
            SymbexPath path = results.get(index++);
            assertEquals("Post", path.getPathIdentifier());
            assertEquals(4, path.getPathConditions().size());
         //   assertEquals("(LET (VAR a b) $res_multiReturn_1 $res_multiReturn_2 (&& (== a 1) (== b 2)))",
         //           path.getPathConditions().getLast().getExpression().toStringTree());
            assertEquals("[(== c c)]",
                    path.getProofObligations().map(x -> x.getExpression().toStringTree()).toString());
            assertEquals("[(ASSIGN $mod (CALL $freshObjects (ARGS $heap))), (ASSIGN $decr 0), (ASSIGN $oldheap $heap), " +
                            "(ASSIGN x $res_CallMe_1), (ASSIGN y $res_CallMe_2), " +
                            "(ASSIGN $heap (CALL $anon (ARGS $heap (LET (VAR this p) c 24 (SETEX this)) $aheap_1))), " +
                            "(ASSIGN x $res_multiReturn_1), (ASSIGN y $res_multiReturn_2)]",
                    path.getAssignmentHistory().map(DafnyTree::toStringTree).toString());
        }
        {
            SymbexPath path = results.get(index++);
            assertEquals("EstPre[multiReturn]", path.getPathIdentifier());
            assertEquals(3, path.getPathConditions().size());
            assertEquals(6, path.getAssignmentHistory().size());
            assertEquals("[(LET (VAR a b) $res_multiReturn_1 $res_multiReturn_2 (== 42 42))]",
                    path.getProofObligations().map(x -> x.getExpression().toStringTree()).toString());
        }
        assertEquals(index, results.size());
    }

    // identified a bug
    @Test
    public void testRecursiveMethodCalls() throws Exception {
        InputStream stream = getClass().getResourceAsStream("methodCalls.dfy");
        DafnyTree fileTree = ParserTest.parseFile(stream);

        // performs type analysis etc:
        Project project = TestUtil.mockProject(fileTree);

        DafnyTree tree = project.getMethod("recursive").getRepresentation();
        Symbex symbex = new Symbex();
        List<SymbexPath> results = symbex.symbolicExecution(tree);

        assertEquals(4, results.size());
        int index = 0;
        {
            SymbexPath path = results.get(index++);
            assertEquals("else/Post", path.getPathIdentifier());
            assertEquals(3, path.getPathConditions().size());
            assertEquals("[(>= n 0), (not (== n 0)), (LET (VAR r n) $res_recursive_1 (- n 1) (== r 0))]",
                    path.getPathConditions().map(x -> x.getExpression().toStringTree()).toString());
            assertEquals("[(ASSIGN $mod (CALL $freshObjects (ARGS $heap))), (ASSIGN $decr (* 2 n)), (ASSIGN $oldheap $heap), (ASSIGN r $res_recursive_1)]",
                    path.getAssignmentHistory().map(DafnyTree::toStringTree).toString());
            assertEquals("[(== r 0)]",
                    path.getProofObligations().map(x -> x.getExpression().toStringTree()).toString());
        }
        {
            SymbexPath path = results.get(index++);
            assertEquals("then/Post", path.getPathIdentifier());
            assertEquals(2, path.getPathConditions().size());
            assertEquals("[(>= n 0), (== n 0)]",
                    path.getPathConditions().map(x -> x.getExpression().toStringTree()).toString());
            assertEquals("[(ASSIGN $mod (CALL $freshObjects (ARGS $heap))), (ASSIGN $decr (* 2 n)), (ASSIGN $oldheap $heap), (:= r n)]",
                    path.getAssignmentHistory().map(DafnyTree::toStringTree).toString());
            assertEquals("[(== r 0)]",
                    path.getProofObligations().map(x -> x.getExpression().toStringTree()).toString());
        }
        {
            SymbexPath path = results.get(index++);
            assertEquals("else/EstPre[recursive]", path.getPathIdentifier());
            assertEquals(2, path.getPathConditions().size());
            assertEquals("[(>= n 0), (not (== n 0))]",
                    path.getPathConditions().map(x -> x.getExpression().toStringTree()).toString());
            assertEquals("[(ASSIGN $mod (CALL $freshObjects (ARGS $heap))), (ASSIGN $decr (* 2 n)), (ASSIGN $oldheap $heap)]",
                    path.getAssignmentHistory().map(DafnyTree::toStringTree).toString());
            assertEquals("[(LET (VAR r n) $res_recursive_1 (- n 1) (>= n 0))]",
                    path.getProofObligations().map(x -> x.getExpression().toStringTree()).toString());
        }
        {
            SymbexPath path = results.get(index++);

            assertEquals("else/Dec[recursive]", path.getPathIdentifier());
            assertEquals(2, path.getPathConditions().size());
            assertEquals("[(>= n 0), (not (== n 0))]",
                    path.getPathConditions().map(x -> x.getExpression().toStringTree()).toString());
            assertEquals("[(ASSIGN $mod (CALL $freshObjects (ARGS $heap))), (ASSIGN $decr (* 2 n)), (ASSIGN $oldheap $heap)]",
                    path.getAssignmentHistory().map(DafnyTree::toStringTree).toString());
            assertEquals("[(LET (VAR r n) $res_recursive_1 (- n 1) (NOETHER_LESS (LISTEX (LET (VAR r n) $res_recursive_1 (- n 1) (* 2 n))) (LISTEX $decr)))]",
                    path.getProofObligations().map(x -> x.getExpression().toStringTree()).toString());
        }
    }

    @Test
    public void testObjectMethodCall() throws Exception {
        InputStream stream = getClass().getResourceAsStream("methodCalls.dfy");
        DafnyTree fileTree = ParserTest.parseFile(stream);

        // performs type analysis etc:
        Project project = TestUtil.mockProject(fileTree);

        DafnyTree tree = project.getMethod("objectReturn").getRepresentation();
        Symbex symbex = new Symbex();
        List<SymbexPath> results = symbex.symbolicExecution(tree);
        int index = 0;
        {
            SymbexPath path = results.get(index++);
            assertEquals("else/Post", path.getPathIdentifier());

            assertEquals("[(not b), " +
                            "(LET (VAR o b) $res_objectReturn_1 true (CALL $isCreated (ARGS $heap o))), " +
                            "(LET (VAR o b) $res_objectReturn_1 true true)]",
                    path.getPathConditions().map(x -> x.getExpression().toStringTree()).toString());

            assertEquals("[(ASSIGN $mod (CALL $freshObjects (ARGS $heap))), (ASSIGN $decr 0), (ASSIGN $oldheap $heap), " +
                            "(ASSIGN $heap (CALL $anon (ARGS $heap (LET (VAR o b) $res_objectReturn_1 true SETEX) $aheap_1))), " +
                            "(ASSIGN o $res_objectReturn_1)]",
                    path.getAssignmentHistory().map(x -> x.toStringTree()).toString());
        }
        {
            SymbexPath path = results.get(index++);
            assertEquals("then/Post", path.getPathIdentifier());
        }
        {
            SymbexPath path = results.get(index++);
            assertEquals("then/Modifies", path.getPathIdentifier());
        }
        {
            SymbexPath path = results.get(index++);
            assertEquals("else/Dec[objectReturn]", path.getPathIdentifier());
        }
        {
            SymbexPath path = results.get(index++);
            assertEquals("else/Modifies[objectReturn]", path.getPathIdentifier());
        }
        {
            SymbexPath path = results.get(index++);
            assertEquals("then/Null", path.getPathIdentifier());
        }
        assertEquals(index, results.size());
    }

    @Test
    public void testFieldAssignment() throws Exception {
        InputStream stream = getClass().getResourceAsStream("fieldAssignment.dfy");
        DafnyTree fileTree = ParserTest.parseFile(stream);

        // performs type analysis etc:
        Project project = TestUtil.mockProject(fileTree);

        DafnyTree tree = project.getMethod("getNumber").getRepresentation();
        DafnyTree code = tree.getFirstChildWithType(DafnyParser.BLOCK);
        Symbex symbex = new Symbex();
        List<SymbexPath> paths = symbex.symbolicExecution(tree);

        assertEquals(3, paths.size());
        {
            SymbexPath path = paths.get(0);

            assertEquals("[PRE[null]:(!= o null)]",
                    path.getPathConditions().toString());

            assertEquals("[(ASSIGN $mod (+ ({ o) (CALL $freshObjects (ARGS $heap)))), (ASSIGN $decr 0), (ASSIGN $oldheap $heap), (:= (FIELD_ACCESS o y) 8)]",
                    path.getAssignmentHistory().map(x -> x.toStringTree()).toString());

            assertEquals("[POST:(> (FIELD_ACCESS o y) 5)]",
                    path.getProofObligations().toString());
        }
        {
            SymbexPath path = paths.get(1);

            assertEquals("[PRE[null]:(!= o null)]",
                    path.getPathConditions().toString());

            assertEquals("[(ASSIGN $mod (+ ({ o) (CALL $freshObjects (ARGS $heap)))), (ASSIGN $decr 0), (ASSIGN $oldheap $heap)]",
                    path.getAssignmentHistory().map(x -> x.toStringTree()).toString());

            assertEquals("[MODIFIES:(IN o $mod)]",
                    path.getProofObligations().toString());
        }
        {
            SymbexPath path = paths.get(2);

            assertEquals("[PRE[null]:(!= o null)]",
                    path.getPathConditions().toString());

            assertEquals("[(ASSIGN $mod (+ ({ o) (CALL $freshObjects (ARGS $heap)))), (ASSIGN $decr 0), (ASSIGN $oldheap $heap)]",
                    path.getAssignmentHistory().map(x -> x.toStringTree()).toString());

            assertEquals("[RT_NONNULL:(!= o null)]",
                    path.getProofObligations().toString());
        }

    }

    @Test
    public void testObjectCreation() throws Exception {
        InputStream stream = getClass().getResourceAsStream("objectCreation.dfy");
        DafnyTree fileTree = ParserTest.parseFile(stream);

        // performs type analysis etc:
        Project project = TestUtil.mockProject(fileTree);

        DafnyTree tree = project.getMethod("test").getRepresentation();
        DafnyTree code = tree.getFirstChildWithType(DafnyParser.BLOCK);
        Symbex symbex = new Symbex();
        // code[0] is a variable declaration
        {
            Deque<SymbexPath> stack = new LinkedList<SymbexPath>();
            SymbexPath state = new SymbexPath(tree);
            DafnyTree ass = code.getChild(1);
            symbex.handleAssign(stack, state, ass, SOME_PROGRAM);

            assertEquals(1, stack.size());
            state = stack.getFirst();

            assertEquals("[IMPLICIT_ASSUMPTION[null]:(not (CALL $isCreated (ARGS $heap $new_1)))]",
                    state.getPathConditions().toString());

            assertEquals("[(ASSIGN $heap (CALL $create (ARGS $heap $new_1))), (ASSIGN c $new_1)]", state.getAssignmentHistory().map(x -> x.toStringTree()).toString());

            assertEquals(0, state.getProofObligations().size());
        }
        {
            Deque<SymbexPath> stack = new LinkedList<SymbexPath>();
            SymbexPath state = new SymbexPath(tree);
            DafnyTree ass = code.getChild(2);
            symbex.handleAssign(stack, state, ass, SOME_PROGRAM);

            assertEquals(2, stack.size());
            state = stack.removeFirst();

            assertEquals(0, state.getProofObligations().size());
            assertEquals("[IMPLICIT_ASSUMPTION[null]:(not (CALL $isCreated (ARGS $heap $new_1))), " +
                            "CALL_POST[null]:(LET (VAR this p) $new_1 23 (== this this))]",
                    state.getPathConditions().toString());
            assertEquals("[(ASSIGN $heap (CALL $create (ARGS $heap $new_1))), (ASSIGN c $new_1)]", state.getAssignmentHistory().map(x -> x.toStringTree()).toString());

            state = stack.removeFirst();

            assertEquals("[CALL_PRE[Init]:(LET (VAR this p) $new_1 23 (== p 1))]", state.getProofObligations().toString());
            assertEquals("[IMPLICIT_ASSUMPTION[null]:(not (CALL $isCreated (ARGS $heap $new_1)))]",
                    state.getPathConditions().toString());
            assertEquals("[(ASSIGN $heap (CALL $create (ARGS $heap $new_1)))]", state.getAssignmentHistory().map(x -> x.toStringTree()).toString());
        }
        {
            Deque<SymbexPath> stack = new LinkedList<SymbexPath>();
            SymbexPath state = new SymbexPath(tree);
            DafnyTree ass = code.getChild(3);
            symbex.handleVarDecl(stack, state, ass, SOME_PROGRAM);

            assertEquals(2, stack.size());
            state = stack.removeFirst();

            assertEquals(0, state.getProofObligations().size());
            assertEquals("[IMPLICIT_ASSUMPTION[null]:(not (CALL $isCreated (ARGS $heap $new_1))), " +
                            "CALL_POST[null]:(LET (VAR this p) $new_1 42 (== this this))]",
                    state.getPathConditions().toString());
            assertEquals("[(ASSIGN $heap (CALL $create (ARGS $heap $new_1))), (ASSIGN c2 $new_1)]", state.getAssignmentHistory().map(x -> x.toStringTree()).toString());

            state = stack.removeFirst();

            assertEquals("[CALL_PRE[Init]:(LET (VAR this p) $new_1 42 (== p 1))]", state.getProofObligations().toString());
            assertEquals("[IMPLICIT_ASSUMPTION[null]:(not (CALL $isCreated (ARGS $heap $new_1)))]",
                    state.getPathConditions().toString());
            assertEquals("[(ASSIGN $heap (CALL $create (ARGS $heap $new_1)))]", state.getAssignmentHistory().map(x -> x.toStringTree()).toString());
        }
        {
            Deque<SymbexPath> stack = new LinkedList<SymbexPath>();
            SymbexPath state = new SymbexPath(tree);
            DafnyTree ass = code.getChild(4);
            symbex.handleVarDecl(stack, state, ass, SOME_PROGRAM);

            assertEquals(2, stack.size());
            state = stack.removeFirst();

            assertEquals(0, state.getProofObligations().size());
            assertEquals("[IMPLICIT_ASSUMPTION[null]:(not (CALL $isCreated (ARGS $heap $new_1))), " +
                            "CALL_POST[null]:(LET (VAR r this) $res_Init2_1 $new_1 (== this this))]",
                    state.getPathConditions().toString());
            assertEquals("[(ASSIGN $heap (CALL $create (ARGS $heap $new_1))), (ASSIGN c3 $new_1)]", state.getAssignmentHistory().map(x -> x.toStringTree()).toString());

            state = stack.removeFirst();

            assertEquals("[CALL_PRE[Init2]:(LET (VAR r this) $res_Init2_1 $new_1 (== 1 1))]", state.getProofObligations().toString());
            assertEquals("[IMPLICIT_ASSUMPTION[null]:(not (CALL $isCreated (ARGS $heap $new_1)))]",
                    state.getPathConditions().toString());
            assertEquals("[(ASSIGN $heap (CALL $create (ARGS $heap $new_1)))]", state.getAssignmentHistory().map(x -> x.toStringTree()).toString());
        }
        {
            Deque<SymbexPath> stack = new LinkedList<SymbexPath>();
            SymbexPath state = new SymbexPath(tree);
            DafnyTree ass = code.getChild(5);
            symbex.handleVarDecl(stack, state, ass, SOME_PROGRAM);

            assertEquals(2, stack.size());
            state = stack.removeFirst();

            assertEquals(0, state.getProofObligations().size());
            assertEquals("[IMPLICIT_ASSUMPTION[null]:(not (CALL $isCreated (ARGS $heap $new_1))), " +
                            "IMPLICIT_ASSUMPTION[null]:(== (Length $new_1) 10)]",
                    state.getPathConditions().toString());
            assertEquals("[(ASSIGN $heap (CALL $create (ARGS $heap $new_1))), (ASSIGN c4 $new_1)]", state.getAssignmentHistory().map(x -> x.toStringTree()).toString());

            state = stack.removeFirst();

            assertEquals("[RT_IN_BOUNDS:(>= 10 0)]", state.getProofObligations().toString());
            assertEquals("[]", state.getPathConditions().toString());
            assertEquals("[]", state.getAssignmentHistory().map(x -> x.toStringTree()).toString());
        }
        // code[6] is variable declaration
        {
            Deque<SymbexPath> stack = new LinkedList<SymbexPath>();
            SymbexPath state = new SymbexPath(tree);
            DafnyTree ass = code.getChild(7);
            symbex.handleVarDecl(stack, state, ass, SOME_PROGRAM);

            assertEquals(3, stack.size());
            state = stack.removeFirst();

            assertEquals(0, state.getProofObligations().size());
            assertEquals("[IMPLICIT_ASSUMPTION[null]:(not (CALL $isCreated (ARGS $heap $new_1))), " +
                            "IMPLICIT_ASSUMPTION[null]:(== (Length $new_1) (Length c4))]",
                    state.getPathConditions().toString());
            assertEquals("[(ASSIGN $heap (CALL $create (ARGS $heap $new_1))), (ASSIGN c5 $new_1)]", state.getAssignmentHistory().map(x -> x.toStringTree()).toString());

            state = stack.removeFirst();

            assertEquals("[RT_IN_BOUNDS:(>= (Length c4) 0)]", state.getProofObligations().toString());
            assertEquals("[]", state.getPathConditions().toString());
            assertEquals("[]", state.getAssignmentHistory().map(x -> x.toStringTree()).toString());

            state = stack.removeFirst();

            assertEquals("[RT_NONNULL:(!= c4 null)]", state.getProofObligations().toString());
            assertEquals("[]", state.getPathConditions().toString());
            assertEquals("[]", state.getAssignmentHistory().map(x -> x.toStringTree()).toString());
        }
    }

    @Test
    public void testHandleReturn() throws Exception {
        InputStream stream = getClass().getResourceAsStream("return.dfy");
        DafnyTree fileTree = ParserTest.parseFile(stream);

        // performs type analysis etc:
        Project project = TestUtil.mockProject(fileTree);

        DafnyTree tree = project.getMethod("m").getRepresentation();
        DafnyTree code = tree.getFirstChildWithType(DafnyParser.BLOCK);
        Symbex symbex = new Symbex();
        List<SymbexPath> paths = symbex.symbolicExecution(tree);

        assertEquals(4, paths.size());
        int cnt = 0;
        assertEquals(AssertionType.INVARIANT_INITIALLY_VALID, paths.get(cnt++).getCommonProofObligationType());
        assertEquals(null, paths.get(cnt++).getCommonProofObligationType());
        assertEquals(AssertionType.POST, paths.get(cnt++).getCommonProofObligationType());
        assertEquals(AssertionType.POST, paths.get(cnt++).getCommonProofObligationType());

        {
            // first return statement
            SymbexPath path = paths.get(2);
            assertEquals("[(ASSIGN $mod (CALL $freshObjects (ARGS $heap))), (ASSIGN $decr 0), (ASSIGN $oldheap $heap), (ASSIGN v WILDCARD), " +
                            "(ASSIGN $decr_1 v)]",
                    path.getAssignmentHistory().map(x -> x.toStringTree()).toString());
            assertEquals("[(== 1 1)]",
                    path.getProofObligations().map(x -> x.getExpression().toStringTree()).toString());
        }
        {
            // first return statement
            SymbexPath path = paths.get(3);
            assertEquals("[(ASSIGN $mod (CALL $freshObjects (ARGS $heap))), (ASSIGN $decr 0), (ASSIGN $oldheap $heap), (ASSIGN v WILDCARD)]",
                    path.getAssignmentHistory().map(x -> x.toStringTree()).toString());
            assertEquals("[(== 1 1)]",
                    path.getProofObligations().map(x -> x.getExpression().toStringTree()).toString());
        }
    }

    @Test
    public void testCollectAssignedVars() throws Exception {

        Symbex symbex = new Symbex();
        {
            Project p = TestUtil.mockProject("method n() { } method m() { n(); }");
            DafnyTree t = p.getMethod("m").getBody();
            HashSet<DafnyTree> set = new HashSet<>();
            TestUtil.call(symbex, "collectAssignedVars", t, set);
            assertEquals("[heap]", Util.map(set, DafnyTree::toStringTree).toString());
        }
        {
            Project p = TestUtil.mockProject("method n() returns (x:int) { } " +
                    "method m() { var x:int; x := n(); }");
            DafnyTree t = p.getMethod("m").getBody();
            Set<DafnyTree> set = new HashSet<>();
            TestUtil.call(symbex, "collectAssignedVars", t, set);
            List<String> map = Util.map(set, DafnyTree::toStringTree);
            map.sort(null);
            assertEquals("[(var x (TYPE int)), heap]", map.toString());
        }
        {
            Project p = TestUtil.mockProject("method m() { var x:int; x := 5; }");
            DafnyTree t = p.getMethod("m").getBody();
            HashSet<DafnyTree> set = new HashSet<>();
            TestUtil.call(symbex, "collectAssignedVars", t, set);
            assertEquals("[(var x (TYPE int))]", Util.map(set, DafnyTree::toStringTree).toString());
        }
        {
            Project p = TestUtil.mockProject("function f(): int { 2 } " +
                    "method m() { var x:int; x := f(); }");
            DafnyTree t = p.getMethod("m").getBody();
            HashSet<DafnyTree> set = new HashSet<>();
            TestUtil.call(symbex, "collectAssignedVars", t, set);
            assertEquals("[(var x (TYPE int))]", Util.map(set, DafnyTree::toStringTree).toString());
        }
    }

    @Test
    public void testPrintStatement() throws Exception {
        Symbex symbex = new Symbex();
        Project p = TestUtil.mockProject("method m() ensures 2==2 { print \"1\", \"2\"; assert 1==1; }");
        List<SymbexPath> result = symbex.symbolicExecution(p.getMethod("m").getRepresentation());
        int cnt = 0;
        assertEquals(AssertionType.EXPLICIT_ASSERT, result.get(cnt++).getCommonProofObligationType());
        assertEquals(AssertionType.POST, result.get(cnt++).getCommonProofObligationType());
        assertEquals(cnt, result.size());
    }

    @Test
    public void testThisAssignment() throws Exception {
        Symbex symbex = new Symbex();
        Project p = TestUtil.mockProject("class C { var fld:C; method m() ensures true { fld := this; this.fld := this; } }");
        List<SymbexPath> result = symbex.symbolicExecution(p.getClass("C").getMethod("m").getRepresentation());
        assertEquals(1, result.size());
        SymbexPath path = result.get(0);
        assertEquals(AssertionType.POST, path.getCommonProofObligationType());
        assertEquals("[(ASSIGN $mod (CALL $freshObjects (ARGS $heap))), (ASSIGN $decr 0), (ASSIGN $oldheap $heap), " +
                "(:= fld this), (:= (FIELD_ACCESS this fld) this)]",
                path.getAssignmentHistory().map(DafnyTree::toStringTree).toString());
    }

    // bug: sequence updates were not captured as assignments!
    @Test
    public void testSequenceUpdate() throws Exception {
        Symbex symbex = new Symbex();
        Project p = TestUtil.mockProject("" +
                "class C { var f: seq<int>;" +
                "  method m() ensures true { " +
                "  var r, s: seq<int>; while(true) { " +
                "    r[0]:=42; s:= r; f[0]:=23;" +
                "}}}");
        List<SymbexPath> result = symbex.symbolicExecution(
                p.getClass("C").getMethod("m").getRepresentation());
        SymbexPath path = result.get(2);
        assertEquals(AssertionType.POST, path.getCommonProofObligationType());
        assertThat(Util.map(path.getAssignmentHistory(), DafnyTree::toStringTree),
                TestUtil.contains("(ASSIGN s WILDCARD)"));
        assertThat(Util.map(path.getAssignmentHistory(), DafnyTree::toStringTree),
                TestUtil.contains("(ASSIGN $heap (CALL $anon (ARGS $heap $mod $aheap_1)))"));
        assertThat(Util.map(path.getAssignmentHistory(), DafnyTree::toStringTree),
                TestUtil.contains("(ASSIGN r WILDCARD)"));
    }

    @Test
    public void testCrossClass() throws Exception {
        InputStream stream = getClass().getResourceAsStream("crossClass.dfy");
        DafnyTree fileTree = ParserTest.parseFile(stream);

        Project project = TestUtil.mockProject(fileTree);
        Symbex symbex = new Symbex();
        DafnyMethod method = project.getClass("C").getMethod("setD");
        List<SymbexPath> result = symbex.symbolicExecution(method.getRepresentation());
        int cnt = 0;
        {
            SymbexPath path = result.get(cnt++);
            assertEquals(AssertionType.POST, path.getCommonProofObligationType());
            assertEquals("[(ASSIGN $mod (+ (SETEX this x) (CALL $freshObjects (ARGS $heap)))), " +
                            "(ASSIGN $decr 0), " +
                            "(ASSIGN $oldheap $heap), " +
                            "(:= (FIELD_ACCESS this d) x), " +
                            "(:= d x), " +
                            "(:= (FIELD_ACCESS x c) this)]",
                    path.getAssignmentHistory().map(DafnyTree::toStringTree).toString());
        }
    }

}