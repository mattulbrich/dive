package edu.kit.iti.algover.nuscript;

import de.uka.ilkd.pp.NoExceptions;
import edu.kit.iti.algover.nuscript.ScriptAST.ByClause;
import edu.kit.iti.algover.nuscript.ScriptAST.Case;
import edu.kit.iti.algover.nuscript.ScriptAST.Cases;
import edu.kit.iti.algover.nuscript.ScriptAST.Command;
import edu.kit.iti.algover.nuscript.ScriptAST.Script;
import edu.kit.iti.algover.nuscript.ScriptAST.Statement;
import edu.kit.iti.algover.nuscript.parser.ScriptParser;
import edu.kit.iti.algover.nuscript.parser.ScriptParser.ScriptContext;
import edu.kit.iti.algover.nuscript.parser.Scripts;
import edu.kit.iti.algover.script.ScriptParserTest;
import edu.kit.iti.algover.util.sealable.SealedException;
import org.junit.Before;
import org.junit.Test;

import java.util.List;

import static org.junit.Assert.*;

public class ScriptASTTest {

    private Script script;

    @Before
    public void makeScript() {
        this.script = Scripts.parseScript("command1 param1='term1' param2=22 by { command2; }\n" +
                "cmd3; cases { case \"A\": skip; }");
    }

    @Test
    public void testSealed() throws Exception {
        assertFalse(script.isSealed());
        script.seal();
        assertTrue(script.isSealed());
        for (Statement statement : script.getStatements()) {
            assertTrue(statement.isSealed());
        }
        Command cmd = (Command)script.getStatements().get(0);
        assertTrue(cmd.isSealed());
        ByClause bc = cmd.getByClause();
        assertTrue(bc.isSealed());
        assertTrue(bc.getStatements().get(0).isSealed());
        Cases cases = (Cases) script.getStatements().get(2);
        assertTrue(cases.isSealed());
        Case aCase = cases.getCases().get(0);
        assertTrue(aCase.isSealed());
        assertTrue(aCase.getStatements().get(0).isSealed());
    }

    @Test
    public void testSealViolation() throws Exception {

        script.seal();

        shouldFail(() -> script.setParent(null));
        shouldFail(() -> script.addStatement(null));
        shouldFail(() -> script.getStatements().add(null));
        shouldFail(() -> script.setRangeFrom(new ScriptContext(null, 0)));
        Command cmd = (Command)script.getStatements().get(0);
        shouldFail(() -> cmd.setProofNode(null));
        shouldFail(() -> cmd.setByClause(null));
        shouldFail(() -> cmd.addParameter(null));
        shouldFail(() -> cmd.getParameters().add(null));
    }

    private void shouldFail(Runnable run) {
        try {
            run.run();
            fail("Should have failed with a SealedException");
        } catch (SealedException ex) {
            // ok, continue
        }
    }
}