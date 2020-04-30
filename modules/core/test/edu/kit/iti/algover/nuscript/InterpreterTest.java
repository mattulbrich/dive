package edu.kit.iti.algover.nuscript;

import edu.kit.iti.algover.data.BuiltinSymbols;
import edu.kit.iti.algover.data.MapSymbolTable;
import edu.kit.iti.algover.parser.DafnyException;
import edu.kit.iti.algover.parser.DafnyParserException;
import edu.kit.iti.algover.project.Project;
import edu.kit.iti.algover.proof.PVC;
import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.term.FunctionSymbol;
import edu.kit.iti.algover.term.Sequent;
import edu.kit.iti.algover.term.Sort;
import edu.kit.iti.algover.term.parser.TermParser;
import edu.kit.iti.algover.util.ProofMockUtil;
import edu.kit.iti.algover.util.TestUtil;
import junitparams.JUnitParamsRunner;
import org.antlr.runtime.RecognitionException;
import org.junit.Before;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.ExpectedException;
import org.junit.runner.RunWith;

import java.io.IOException;
import java.util.ArrayList;
import java.util.Collection;

import static org.junit.Assert.*;

public class InterpreterTest {

    private MapSymbolTable symbTable;

    @Rule
    public ExpectedException thrown = ExpectedException.none();

    @Before
    public void setupTable() throws DafnyParserException, RecognitionException, IOException, DafnyException {
        Collection<FunctionSymbol> map = new ArrayList<>();
        map.add(new FunctionSymbol("i1", Sort.INT));
        map.add(new FunctionSymbol("i2", Sort.INT));
        map.add(new FunctionSymbol("i3", Sort.INT));
        map.add(new FunctionSymbol("b1", Sort.BOOL));
        map.add(new FunctionSymbol("b2", Sort.BOOL));
        map.add(new FunctionSymbol("b3", Sort.BOOL));
        symbTable = new MapSymbolTable(new BuiltinSymbols(), map);
    }


    @Test
    public void testSplit() throws Exception {

        Project p = TestUtil.mockProject("method m(b1: bool) ensures b1&&b1 { }");
        PVC pvc = p.getPVCByName("m/Post");
        ProofNode root = ProofNode.createRoot(pvc);
        Interpreter interpreter = new Interpreter(root);
        interpreter.interpret("skip; andRight;");

        assertEquals(1, root.getChildren().size());

        ProofNode child = root.getChildren().get(0);
        assertEquals(2, child.getChildren().size());

        assertFalse(root.isClosed());
        assertFalse(child.isClosed());
    }


    @Test
    public void testClosed() throws Exception {

        Project p = TestUtil.mockProject("method m(b1: bool) ensures b1 { }");
        PVC pvc = p.getPVCByName("m/Post");
        ProofNode root = ProofNode.createRoot(pvc);
        Interpreter interpreter = new Interpreter(root);
        interpreter.interpret("skip; fake close=true;");

        assertEquals(1, root.getChildren().size());

        ProofNode child = root.getChildren().get(0);
        assertEquals(0, child.getChildren().size());

        assertFalse(root.isClosed());
        assertTrue(child.isClosed());

        assertTrue(root.allLeavesClosed());
        assertTrue(child.allLeavesClosed());
    }

    @Test
    public void testNotMatching() throws Exception {
        Project p = TestUtil.mockProject("method m(b1: bool) ensures b1 == b1 { }");
        PVC pvc = p.getPVCByName("m/Post");
        ProofNode root = ProofNode.createRoot(pvc);
        Interpreter interpreter = new Interpreter(root);

        thrown.expect(ScriptException.class);
        thrown.expectMessage("Schematic sequent |- (?match: $and(_, _)) does not match.");

        interpreter.interpret("andRight;");
    }

    @Test
    public void testUnknownCommand() throws Exception {
        Project p = TestUtil.mockProject("method m(b1: bool) ensures b1 == b1 { }");
        PVC pvc = p.getPVCByName("m/Post");
        ProofNode root = ProofNode.createRoot(pvc);
        Interpreter interpreter = new Interpreter(root);

        thrown.expect(ScriptException.class);
        thrown.expectMessage("Unknown script command unknownCommand");

        interpreter.interpret("unknownCommand;");
    }
}