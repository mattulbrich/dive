package edu.kit.iti.algover.symbex;

import static org.junit.Assert.*;

import java.io.InputStream;
import java.util.ArrayList;
import java.util.Deque;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;

import org.antlr.runtime.CommonToken;
import org.junit.Before;
import org.junit.Test;

import edu.kit.iti.algover.parser.ParserTest;
import edu.kit.iti.algover.parser.DafnyParser;
import edu.kit.iti.algover.parser.DafnyTree;
import edu.kit.iti.algover.symbex.PathConditionElement.AssertionType;
import edu.kit.iti.algover.symbex.PathConditionElement.AssumptionType;

public class SymbexTest {

    private static final VariableMap SOME_MAP =
            VariableMap.EMPTY.assign("var", new DafnyTree(new CommonToken(-4)));

    private DafnyTree tree;

    private static final DafnyTree SOME_PROGRAM =
            new DafnyTree(new CommonToken(-1, "SOME PROGRAM"));

    @Before
    public void loadTree() throws Exception {
        InputStream stream = getClass().getResourceAsStream("symbex");
        this.tree = ParserTest.parseFile(stream);
    }

    @Test
    public void testSymbolicExecution() throws Exception {

        Symbex symbex = new Symbex();
        List<SymbexState> results = symbex.symbolicExecution(tree);

        System.out.println(results);

        assertEquals(5, results.size());

        assertEquals(AssertionType.INVARIANT_INITIALLY_VALID, results.get(0).getProofObligationType());
        assertEquals(AssertionType.INVARIANT_PRESERVED, results.get(1).getProofObligationType());
        assertEquals(AssertionType.ASSERT, results.get(2).getProofObligationType());
        assertEquals(AssertionType.POST, results.get(3).getProofObligationType());
        assertEquals(AssertionType.POST, results.get(4).getProofObligationType());
    }

    @Test
    public void testHandleAssert() {

        DafnyTree assertionStm = tree.getLastChild().getChild(4);
        assertEquals(DafnyParser.ASSERT, assertionStm.getType());

        Symbex symbex = new Symbex();
        Deque<SymbexState> stack = new LinkedList<SymbexState>();
        List<SymbexState> results = new ArrayList<SymbexState>();
        SymbexState state = new SymbexState(tree);
        state.setMap(SOME_MAP);
        symbex.handleAssert(stack , results , state, assertionStm, SOME_PROGRAM);

        assertEquals(1, stack.size());
        assertEquals(1, results.size());

        SymbexState next = stack.pop();
        assertTrue(next.getBlockToExecute() == SOME_PROGRAM);
        assertTrue(next.getMap() == SOME_MAP);
        assertEquals(0, next.getPathConditions().size());

        SymbexState check = results.get(0);
        assertEquals(AssertionType.ASSERT, check.getProofObligationType());
        assertEquals(1, check.getProofObligations().size());
        assertEquals("(assert (== unmodifiedInLoop 0))", check.getProofObligations().iterator().next().toStringTree());
    }

    @Test
    public void testHandleAssignment() {
        DafnyTree assStm = tree.getLastChild().getChild(0);
        assertEquals(DafnyParser.ASSIGN, assStm.getType());

        Symbex symbex = new Symbex();
        Deque<SymbexState> stack = new LinkedList<SymbexState>();
        List<SymbexState> results = new ArrayList<SymbexState>();
        SymbexState state = new SymbexState(tree);
        state.setMap(SOME_MAP);

        symbex.handleAssign(stack, state, assStm, SOME_PROGRAM);

        assertEquals(1, stack.size());
        assertEquals(0, results.size());

        SymbexState next = stack.pop();
        assertTrue(next.getBlockToExecute() == SOME_PROGRAM);
        assertEquals("1", next.getMap().get("count").toStringTree());
        assertEquals(0, next.getPathConditions().size());
    }

    @Test
    public void testHandleWhile() {
        DafnyTree whileStm = tree.getLastChild().getChild(2);
        assertEquals(DafnyParser.WHILE,  whileStm.getType());

        Symbex symbex = new Symbex();
        Deque<SymbexState> stack = new LinkedList<SymbexState>();
        List<SymbexState> results = new ArrayList<SymbexState>();
        SymbexState state = new SymbexState(tree);
        state.setProofObligations(tree.getChild(3).getLastChild(), AssertionType.POST);
        state.setMap(SOME_MAP);

        symbex.handleWhile(stack, results, state, whileStm, SOME_PROGRAM);

        assertEquals(2, stack.size());
        assertEquals(1, results.size());

        {
            SymbexState init = results.get(0);
            assertEquals(AssertionType.INVARIANT_INITIALLY_VALID, init.getProofObligationType());
            assertEquals(0, init.getPathConditions().size());
            assertEquals(1, init.getProofObligations().size());
            assertEquals("(invariant (== p 2))", init.getProofObligations().iterator().next().toStringTree());
        }

        {
            SymbexState pres = stack.pop();
            {
                assertEquals(2, pres.getPathConditions().size());
                Iterator<PathConditionElement> pcIt = pres.getPathConditions().iterator();
                {
                    PathConditionElement pc1 = pcIt.next();
                    assertEquals("(> p 1)", pc1.getExpression().toStringTree());
                    assertEquals(AssumptionType.WHILE_TRUE, pc1.getType());
                }
                {
                    PathConditionElement pc2 = pcIt.next();
                    assertEquals("(== p 2)", pc2.getExpression().toStringTree());
                    assertEquals(AssumptionType.ASSUMED_INVARIANT, pc2.getType());
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
            SymbexState cont = stack.pop();
            assertEquals(AssertionType.POST, cont.getProofObligationType());
            assertEquals(2, cont.getPathConditions().size());
            Iterator<PathConditionElement> pcIt = cont.getPathConditions().iterator();
            {
                PathConditionElement pc1 = pcIt.next();
                assertEquals("(not (> p 1))", pc1.getExpression().toStringTree());
                assertEquals(AssumptionType.WHILE_FALSE, pc1.getType());
            }
            {
                PathConditionElement pc2 = pcIt.next();
                assertEquals("(== p 2)", pc2.getExpression().toStringTree());
                assertEquals(AssumptionType.ASSUMED_INVARIANT, pc2.getType());
            }
            {
                assertEquals(AssertionType.POST, cont.getProofObligationType());
                assertEquals(1, cont.getProofObligations().size());
                DafnyTree po = cont.getProofObligations().iterator().next();
                assertEquals("(> p 0)", po.toStringTree());
            }
        }
    }

    @Test
    public void testHandleWhileAnonymisation() {
        fail("to do");
    }
}