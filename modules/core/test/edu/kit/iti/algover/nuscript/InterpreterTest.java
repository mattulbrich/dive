package edu.kit.iti.algover.nuscript;

import edu.kit.iti.algover.data.BuiltinSymbols;
import edu.kit.iti.algover.data.MapSymbolTable;
import edu.kit.iti.algover.parser.DafnyException;
import edu.kit.iti.algover.parser.DafnyParserException;
import edu.kit.iti.algover.project.Project;
import edu.kit.iti.algover.proof.PVC;
import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.term.FunctionSymbol;
import edu.kit.iti.algover.term.Sort;
import edu.kit.iti.algover.util.TestUtil;
import org.antlr.runtime.RecognitionException;
import org.junit.Before;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.ExpectedException;

import java.io.IOException;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

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

        assertEquals("-- skip ('case 1':andRight 'case 2':andRight )", toTreeString(root));
    }

    @Test
    public void testCases() throws Exception {

        Project p = TestUtil.mockProject("method m(b1: bool) ensures b1 && b1 { }");
        PVC pvc = p.getPVCByName("m/Post");
        ProofNode root = ProofNode.createRoot(pvc);
        Interpreter interpreter = new Interpreter(root);
        interpreter.interpret("andRight; cases { case \"case 1\": skip; fake close=true; }");

        assertEquals(2, root.getChildren().size());
        assertFalse(root.allLeavesClosed());

        ProofNode child1 = root.getChildren().get(1);
        assertNull(child1.getChildren());

        ProofNode child2 = root.getChildren().get(0);
        assertTrue(child2.allLeavesClosed());

        ProofNode child3 = child2.getChildren().get(0);
        assertTrue(child3.allLeavesClosed());
        assertFalse(child3.isClosed());
        assertEquals(1, child3.getChildren().size());

        ProofNode child4 = child3.getChildren().get(0);
        assertTrue(child4.allLeavesClosed());
        assertTrue(child4.isClosed());

        assertEquals("-- ('case 1':andRight skip fake 'case 2':andRight )", toTreeString(root));
    }


    private String toTreeString(ProofNode pn) {
        StringBuilder result = new StringBuilder();
        if (pn.getCommand() != null) {
            result.append(pn.getCommand().getCommand().getText());
        } else {
            result.append("--");
        }
        result.append(" ");
        List<ProofNode> children = pn.getChildren();
        if (children != null) {
            if (children.size() > 1) {
                result.append("(");
                for (ProofNode child : children) {
                    result.append("'" + child.getLabel() + "':");
                    result.append(toTreeString(child));
                }
                result.append(")");
            } else {
                children.forEach(c -> result.append(toTreeString(c)));
            }
        }
        return result.toString();

    }

    @Test
    public void testClosed() throws Exception {

        Project p = TestUtil.mockProject("method m(b1: bool) ensures b1 { }");
        PVC pvc = p.getPVCByName("m/Post");
        ProofNode root = ProofNode.createRoot(pvc);
        Interpreter interpreter = new Interpreter(root);
        interpreter.interpret("fake close=true;");

        assertEquals(1, root.getChildren().size());

        ProofNode child = root.getChildren().get(0);
        assertEquals(0, child.getChildren().size());

        assertFalse(root.isClosed());
        assertTrue(child.isClosed());

        assertTrue(root.allLeavesClosed());
        assertTrue(child.allLeavesClosed());

        assertEquals("-- fake ", toTreeString(root));
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