/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.script;


import edu.kit.iti.algover.data.SymbolTable;
import edu.kit.iti.algover.parser.DafnyFileParser;
import edu.kit.iti.algover.parser.DafnyTree;
import edu.kit.iti.algover.project.Project;
import edu.kit.iti.algover.proof.PVC;
import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.script.ast.*;
import edu.kit.iti.algover.script.data.GoalNode;
import edu.kit.iti.algover.script.data.State;
import edu.kit.iti.algover.script.interpreter.Interpreter;
import edu.kit.iti.algover.script.interpreter.InterpreterBuilder;
import edu.kit.iti.algover.script.parser.Facade;
import edu.kit.iti.algover.term.Sequent;
import edu.kit.iti.algover.util.InterpreterUtils;
import edu.kit.iti.algover.util.TestUtil;
import org.junit.Assert;
import org.junit.Ignore;
import org.junit.Test;

import java.io.*;
import java.util.List;

/**
 * IMPORTANT
 * This test is ignored because atm refactoring is going
 * on on another branch and recent state is not merged completly with master yet
 * Test class for testing the script parser
 */

public class ScriptParserTest {

    static final String testDir = ("modules/core/test-res/edu/kit/iti/algover/script").replace('/', File.separatorChar);
    static final String filename = "project.script";
    ASTNode parsedScript;

        @Test
        @Ignore
        public void testInterpretSimple() throws Exception {
            testParseSimpleScript();
            InterpreterBuilder ib = new InterpreterBuilder();
            ib.startWith(parsedScript);
            //ServiceLoader<> ruleLoader = new ServiceLoader<>();

            SymbolTable setupTable = InterpreterUtils.setupTable();

            DafnyTree t = DafnyFileParser.parse(new ByteArrayInputStream("method dummy() ensures true { }".getBytes()));
            Project p = TestUtil.mockProject(t);

            PVC pvc = p.getAllPVCs().getContents().get(0);

            setupTable.getAllSymbols().forEach(functionSymbol ->
                    pvc.getSymbolTable().addFunctionSymbol(functionSymbol)
            );

            String[] antec = {"b1 ==> b2", "b2 ==> b3"};
            String[] succ = {"b1 && b2", "b2 && b3"};


            Sequent s = InterpreterUtils.createTestSequent(antec, succ, setupTable);

            ib.startState(new ProofNode(null, null, s, pvc));
            Interpreter i = ib.build();

            System.out.println((i.getCurrentState().getSelectedGoalNode()).getSequent());

            i.interpret(parsedScript);

            List<ProofNode> goals = i.getCurrentState().getGoals();
            for (ProofNode n : goals) {
                System.out.println(n.getSequent());
            }


        }


    @Test
    @Ignore
    public void testParseSimpleScript() throws Exception {
        File file = new File(testDir + File.separatorChar + filename);

        if (!file.exists()) {
                throw new FileNotFoundException(filename);
            }
        parsedScript = Facade.getAST(file);
        ProofScript script = (ProofScript) parsedScript;

        Assert.assertNotNull(parsedScript);
        //Assert.assertSame("The Scripts are not identical", 2, script.getBody().size());
        Statement s = script.getBody().get(0);

        //Assert.assertEquals("The first statement is a call statement", "CallStatement", s.getNodeName());
        CallStatement call = (CallStatement) s;
        //Assert.assertEquals("The call statement is a rule command", "andRight", call.getCommand());
        }



}
