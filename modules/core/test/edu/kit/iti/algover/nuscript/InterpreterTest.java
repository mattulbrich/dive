package edu.kit.iti.algover.nuscript;

import edu.kit.iti.algover.data.BuiltinSymbols;
import edu.kit.iti.algover.data.MapSymbolTable;
import edu.kit.iti.algover.nuscript.ScriptAST.Cases;
import edu.kit.iti.algover.nuscript.ScriptAST.Command;
import edu.kit.iti.algover.parser.DafnyException;
import edu.kit.iti.algover.parser.DafnyParserException;
import edu.kit.iti.algover.project.Project;
import edu.kit.iti.algover.proof.PVC;
import edu.kit.iti.algover.proof.Proof;
import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.rules.RuleException;
import edu.kit.iti.algover.term.FunctionSymbol;
import edu.kit.iti.algover.term.Sort;
import edu.kit.iti.algover.util.TestUtil;
import org.antlr.runtime.RecognitionException;
import org.antlr.v4.runtime.misc.ParseCancellationException;
import org.hamcrest.Matchers;
import org.junit.Before;
import org.junit.Test;

import java.io.IOException;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

import static org.junit.Assert.*;

public class InterpreterTest {

    private MapSymbolTable symbTable;

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

        Proof proof = new Proof(pvc);
        Interpreter interpreter = new Interpreter(proof);
        interpreter.interpret("skip; andRight;");
        ProofNode root = interpreter.getRootNode();

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
        Proof proof = new Proof(pvc);
        Interpreter interpreter = new Interpreter(proof);
        ProofNode root = interpreter.getRootNode();
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
        Proof proof = new Proof(pvc);
        Interpreter interpreter = new Interpreter(proof);
        ProofNode root = interpreter.getRootNode();
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
        Proof proof = new Proof(pvc);
        Interpreter interpreter = new Interpreter(proof);
        interpreter.interpret("andRight;");

        assertTrue(interpreter.hasFailure());
        Exception exc = interpreter.getFailures().get(0);
        assertThat(exc, Matchers.instanceOf(ScriptException.class));
        assertThat(exc.getMessage(),
                Matchers.containsString("Schematic sequent |- (?m: $and(_, _)) does not match."));

    }

    @Test
    public void testUnknownCommand() throws Exception {
        Project p = TestUtil.mockProject("method m(b1: bool) ensures b1 == b1 { }");
        PVC pvc = p.getPVCByName("m/Post");
        Proof proof = new Proof(pvc);
        Interpreter interpreter = new Interpreter(proof);
        interpreter.interpret("unknownCommand;");
        assertTrue(interpreter.hasFailure());
        Exception exc = interpreter.getFailures().get(0);
        assertThat(exc, Matchers.instanceOf(ScriptException.class));
        assertThat(exc.getMessage(),
                Matchers.equalToIgnoringCase("Unknown script command unknownCommand"));
    }

    @Test
    public void testUnknownLabel() throws Exception {
        Project p = TestUtil.mockProject("method m(b1: bool) ensures b1 && b1 { }");
        PVC pvc = p.getPVCByName("m/Post");
        Proof proof = new Proof(pvc);
        Interpreter interpreter = new Interpreter(proof);
        interpreter.interpret("andRight; cases { case \"unknownLabel\": skip; }");
        assertTrue(interpreter.hasFailure());
        Exception exc = interpreter.getFailures().get(0);
        assertThat(exc, Matchers.instanceOf(ScriptException.class));
        assertThat(exc.getMessage(),
                Matchers.equalToIgnoringCase("Unknown label \"unknownLabel\""));
    }

    @Test
    public void testWrongCommand() throws Exception {
        Project p = TestUtil.mockProject("method m(b1: bool) ensures b1 || b1 { }");
        PVC pvc = p.getPVCByName("m/Post");
        Proof proof = new Proof(p, pvc);
        Interpreter interpreter = new Interpreter(proof);
        interpreter.interpret("andRight on=S.0;");
        assertTrue(interpreter.hasFailure());
        Exception exc = interpreter.getFailures().get(0);
        assertThat(exc, Matchers.instanceOf(ScriptException.class));
        assertThat(exc.getMessage(),
                Matchers.containsString("andRight may only be applied to terms with operator '&&'"));
    }

    @Test
    public void testSyntaxError() throws Exception {
        Project p = TestUtil.mockProject("method m(b1: bool) ensures true { }");
        PVC pvc = p.getPVCByName("m/Post");
        Proof proof = new Proof(pvc);
        Interpreter interpreter = new Interpreter(proof);
        interpreter.interpret(";;;");
        assertTrue(interpreter.hasFailure());
        Exception exc = interpreter.getFailures().get(0);
        assertThat(exc, Matchers.instanceOf(ParseCancellationException.class));
        assertThat(exc.getMessage(),
                Matchers.containsString("mismatched input ';' expecting <EOF>"));
    }

    @Test
    public void testIllegalAfterSplit() throws Exception {
        Project p = TestUtil.mockProject("method m(b1: bool) ensures b1 && b1 { }");
        PVC pvc = p.getPVCByName("m/Post");
        Proof proof = new Proof(pvc);
        Interpreter interpreter = new Interpreter(proof);
        interpreter.interpret("andRight; skip;");
        assertTrue(interpreter.hasFailure());
        Exception exc = interpreter.getFailures().get(0);
        assertThat(exc, Matchers.instanceOf(ScriptException.class));
        assertThat(exc.getMessage(),
                Matchers.equalToIgnoringCase("Command cannot be applied, there is more than one (or no) open goal"));
    }

    @Test
    public void testUnknownNumberedParameter() throws Exception {
        Project p = TestUtil.mockProject("method m(b1: bool) ensures true { }");
        PVC pvc = p.getPVCByName("m/Post");
        Proof proof = new Proof(pvc);
        Interpreter interpreter = new Interpreter(proof);
        interpreter.interpret("skip \"numbered parameters not supported here\";");
        assertTrue(interpreter.hasFailure());
        Exception exc = interpreter.getFailures().get(0);
        assertThat(exc, Matchers.instanceOf(ScriptException.class));
        assertThat(exc.getMessage(),
                Matchers.containsString("Unknown parameter #1"));
    }

    @Test
    public void testIllegalSelector() throws Exception {
        Project p = TestUtil.mockProject("method m(b1: bool) ensures true { }");
        PVC pvc = p.getPVCByName("m/Post");
        Proof proof = new Proof(pvc);
        Interpreter interpreter = new Interpreter(proof);
        interpreter.interpret("replace on=S.42.1 with='true';");
        assertTrue(interpreter.hasFailure());
        Exception exc = interpreter.getFailures().get(0);
        assertThat(exc, Matchers.instanceOf(ScriptException.class));
        assertThat(exc.getMessage(),
                Matchers.containsString("Cannot select S.42.1 in"));
    }

    @Test
    public void testIllegalTerm() throws Exception {
        Project p = TestUtil.mockProject("method m(b1: bool) ensures true { }");
        PVC pvc = p.getPVCByName("m/Post");
        Proof proof = new Proof(pvc);
        Interpreter interpreter = new Interpreter(proof);
        interpreter.interpret("replace on=S.0 with='strange term not parseable';");
        assertTrue(interpreter.hasFailure());
        Exception exc = interpreter.getFailures().get(0);
        assertThat(exc, Matchers.instanceOf(ScriptException.class));
        assertThat(exc.getMessage(),
                Matchers.containsString("Cannot parse term/sequent 'strange term not parseable'"));
    }

    @Test
    public void testMissingParameter() throws Exception {
        Project p = TestUtil.mockProject("method m(b1: bool) ensures true { }");
        PVC pvc = p.getPVCByName("m/Post");
        Proof proof = new Proof(pvc);
        Interpreter interpreter = new Interpreter(proof);
        interpreter.interpret("replace on=S.0;");
        assertTrue(interpreter.hasFailure());
        Exception exc = interpreter.getFailures().get(0);
        assertThat(exc, Matchers.instanceOf(ScriptException.class));
        assertThat(exc.getMessage(),
                Matchers.containsString("This command is not applicable"));
    }

    @Test
    public void testWrongParameterType() throws Exception {
        Project p = TestUtil.mockProject("method m(b1: bool) ensures true { }");
        PVC pvc = p.getPVCByName("m/Post");
        Proof proof = new Proof(pvc);
        Interpreter interpreter = new Interpreter(proof);
        interpreter.interpret("replace on=\"wrong type\";");
        assertTrue(interpreter.hasFailure());
        Exception exc = interpreter.getFailures().get(0);
        assertThat(exc, Matchers.instanceOf(ScriptException.class));
        assertThat(exc.getMessage(),
                Matchers.containsString("Parameter 'on' expects an argument of type Term, " +
                        "cannot digest 'wrong type'"));
    }

    // was a bug
    @Test
    public void testContinueAfterUnknownCommand() throws Exception {
        Project p = TestUtil.mockProject("method m(b1: bool) ensures b1 == b1 { }");
        PVC pvc = p.getPVCByName("m/Post");
        Proof proof = new Proof(pvc);
        Interpreter interpreter = new Interpreter(proof);
        interpreter.interpret("unknownCommand; skip;");
        assertTrue(interpreter.hasFailure());
        Exception exc = interpreter.getFailures().get(0);
        assertThat(exc, Matchers.instanceOf(ScriptException.class));
        assertThat(exc.getMessage(),
                Matchers.equalToIgnoringCase("Unknown script command unknownCommand"));
    }

    @Test
    public void testProofNodeAssignment() throws Exception {
        Project p = TestUtil.mockProject("method m(b1: bool) ensures b1 && b1 { }");
        PVC pvc = p.getPVCByName("m/Post");
        Proof proof = new Proof(pvc);

        proof.setScriptText("skip; andRight on='|-_'; cases { case \"case 1\": fake; }");
        proof.interpretScript();

        Command skip = (Command) proof.getProofScript().getStatements().get(0);
        assertEquals("skip", skip.getCommand().getText());
        assertSame(proof.getProofRoot(), skip.getProofNode());

        Command andRight = (Command) proof.getProofScript().getStatements().get(1);
        assertEquals("andRight", andRight.getCommand().getText());
        assertSame(proof.getProofRoot().getChildren().get(0), andRight.getProofNode());

        Command innerSkip = (Command) ((Cases)proof.getProofScript().getStatements().get(2)).getCases().get(0).getStatements().get(0);
        assertEquals("fake", innerSkip.getCommand().getText());
        assertSame(proof.getProofRoot().getChildren().get(0).getChildren().get(0), innerSkip.getProofNode());

    }

    @Test
    public void testAfterCases() throws Exception {
        Project p = TestUtil.mockProject("method m(b1: bool) ensures b1 && b1 { }");
        PVC pvc = p.getPVCByName("m/Post");
        Proof proof = new Proof(pvc);

        proof.setScriptText("andRight on='|-_'; cases { case \"case 1\": fake; } skip;");
        proof.interpretScript();

        assertEquals("-- ('case 1':andRight fake 'case 2':andRight skip )",
                toTreeString(proof.getProofRoot()));
    }

    @Test
    public void testBy() throws Exception {
        Project p = TestUtil.mockProject("method m(b1: bool) ensures 1+1 > 1 { }");
        PVC pvc = p.getPVCByName("m/Post");
        Proof proof = new Proof(pvc);
        proof.setScriptText("replace on=S.0.0 with='2' by fake; skip;");
        proof.interpretScript();
        for (Exception exception : proof.getFailures()) {
            exception.printStackTrace();
        }
        assertEquals("-- ('justification':replace fake 'replace':replace skip )",
                toTreeString(proof.getProofRoot()));
    }

    @Test
    public void testIllegalBy() throws Exception {
        Project p = TestUtil.mockProject("method m(b1: bool) ensures true { }");
        PVC pvc = p.getPVCByName("m/Post");
        Proof proof = new Proof(pvc);
        proof.setScriptText("skip by fake;");
        proof.interpretScript();
        Exception exc = proof.getFailures().get(0);
        assertThat(exc, Matchers.instanceOf(ScriptException.class));
        assertThat(exc.getMessage(),
                Matchers.equalToIgnoringCase("by clauses are only allowed for rules with two cases"));
    }

    @Test
    public void testIllegalBy2() throws Exception {
        Project p = TestUtil.mockProject("method m(b1: bool) ensures true { }");
        PVC pvc = p.getPVCByName("m/Post");
        Proof proof = new Proof(pvc);
        proof.setScriptText("fake close=true by skip;");
        proof.interpretScript();
        Exception exc = proof.getFailures().get(0);
        assertThat(exc, Matchers.instanceOf(ScriptException.class));
        assertThat(exc.getMessage(),
                Matchers.equalToIgnoringCase("by clauses are only allowed for rules with two cases"));
    }
}