package edu.kit.iti.algover.script;

import edu.kit.iti.algover.model.FieldLeaf;
import edu.kit.iti.algover.parser.DafnyTree;
import edu.kit.iti.algover.parser.ParserTest;
import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.script.ast.*;
import edu.kit.iti.algover.script.data.GoalNode;
import edu.kit.iti.algover.script.interpreter.Interpreter;
import edu.kit.iti.algover.script.interpreter.InterpreterBuilder;
import edu.kit.iti.algover.script.parser.Facade;
import edu.kit.iti.algover.term.Sequent;
import edu.kit.iti.algover.util.InterpreterUtils;
import edu.kit.iti.algover.util.TestUtil;
import org.junit.Assert;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;

import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.InputStream;
import java.net.URL;
import java.util.Arrays;
import java.util.ServiceLoader;

/**
 * Test class for testing the script parser
 */

public class ScriptParserTest {

    static final String testDir = ("modules/core/test-res/edu/kit/iti/algover/script").replace('/', File.separatorChar);
    static final String filename = "project.script";
    ASTNode parsedScript;

        @Test
        public void testInterpretSimple() throws Exception {
            testParseSimpleScript();
            InterpreterBuilder ib = new InterpreterBuilder();
            ib.startWith(parsedScript);
            //ServiceLoader<> ruleLoader = new ServiceLoader<>();


            String[] antec = {"b1 ==> b2", "b2 ==> b3"};
            String[] succ = {"b1 && b2", "b2&&b3"};
            Sequent s = InterpreterUtils.createTestSequent(antec, succ, InterpreterUtils.setupTable());
            ib.startState(new GoalNode<>(null, new ProofNode(null, null, null, s, null)));
            Interpreter i = ib.build();

            System.out.println(((ProofNode) i.getCurrentState().getSelectedGoalNode().getData()).getSequent());

            i.interpret(parsedScript);

            System.out.println(((ProofNode) i.getCurrentState().getSelectedGoalNode().getData()).getSequent());


        }

    @Test
    public void testParseSimpleScript() throws Exception {
        File file = new File(testDir + File.separatorChar + filename);

        if (!file.exists()) {
                throw new FileNotFoundException(filename);
            }
        parsedScript = Facade.getAST(file);
        ProofScript script = (ProofScript) parsedScript;

        Assert.assertNotNull(parsedScript);
        Assert.assertSame("The Scripts are not identical", 2, script.getBody().size());
        Statement s = script.getBody().get(0);

        Assert.assertEquals("The first statement is a call statement", "CallStatement", s.getNodeName());
        CallStatement call = (CallStatement) s;
        Assert.assertEquals("The call statement is a rule command", "andRight", call.getCommand());
        }



}
