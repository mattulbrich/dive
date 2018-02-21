package edu.kit.iti.algover.rules.impl;

import edu.kit.iti.algover.data.BuiltinSymbols;
import edu.kit.iti.algover.data.SymbolTable;
import edu.kit.iti.algover.parser.DafnyParserException;
import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.rules.*;
import edu.kit.iti.algover.rules.Parameters;
import edu.kit.iti.algover.term.FunctionSymbol;
import edu.kit.iti.algover.term.Sequent;
import edu.kit.iti.algover.term.Sort;
import edu.kit.iti.algover.term.builder.TermBuildException;
import edu.kit.iti.algover.term.parser.TermParser;
import edu.kit.iti.algover.util.Pair;
import edu.kit.iti.algover.util.ProofMockUtil;
import junitparams.JUnitParamsRunner;
import org.junit.Before;
import org.junit.Test;
import org.junit.runner.RunWith;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

/**
 * Created by jklamroth on 2/1/18.
 *
 * This class provides generic tests for rules with ONLY an ON parameter. There are 3 kinds of test:
 *      Applicable: This test expects the rule to be applicable and the result to be equal to the given parameters.
 *      NotApplicable: This test considers the application of the rule but should be not applicable.
 *      Exception: This test tries to make the application of the given rule but excepts a RuleException as result.
 *
 * To add test simply add an entry to the respective parameters.
 *
 */
@RunWith(JUnitParamsRunner.class)
public class GenericRuleTest {
    SymbolTable symbolTable;

    /**
     * Structure is as follows:
     *      - the rule to be tested
     *      - the sequent the rule is tested on
     *      - a TermSelector pointing to the selected term (used as on-paramter)
     *      - a list of resulting sequences given as strings (the size of results has to match the number of branches
     *        created by the rule application and each branch has to be contained in results)
     *      - optional: New function symbols (Pair<String, Sort>(name, Sort)), if null this defaults to the preinitialized
     *      ones: boolean variables b1,...,b4, int variables i1,...,i4
     * @return parameters for the applicable-Test
     */
    public Object [][] parametersForGenericRuleTestApplicable() {
        ProofRule pr = null;
        try {
            pr = DafnyRuleUtil.generateDafnyRuleFromFile("./modules/core/test-res/edu/kit/iti/algover/dafnyrules/addzero2.dfy");
        } catch(DafnyRuleException e) {
            System.out.println("Error creating DafnyRule.");
            e.printStackTrace();
            return new Object[0][0];
        }
        return new Object[][] {
                {new OrLeftRule(), "b1 || b2 |- b1", new TermSelector(TermSelector.SequentPolarity.ANTECEDENT, 0),
                        new ArrayList<>(Arrays.asList("[b1] ==> [b1]", "[b2] ==> [b1]")), null},
                {pr, "i1 + i2 == 0  |- i3 == 0", new TermSelector(TermSelector.SequentPolarity.ANTECEDENT, 0, 0),
                        new ArrayList<>(Arrays.asList("[$eq<int>(i1, 0)] ==> [$eq<int>(i3, 0)]", "[$eq<int>($plus(i1, i2), 0)] ==> [$eq<int>(i2, 0)]")), null},
                {pr, "i1 + i2 == 0, i2 == 0  |- i1 == 0", new TermSelector(TermSelector.SequentPolarity.ANTECEDENT, 0, 0),
                        new ArrayList<>(Arrays.asList("[$eq<int>(i1, 0), $eq<int>(i2, 0)] ==> [$eq<int>(i1, 0)]")), null},

        };
    }

    public Object [][] parametersForGenericRuleTestNotApplicable() {
        return new Object[][] {
                {new OrLeftRule(), "b1 || b2 |- b1", new TermSelector(TermSelector.SequentPolarity.SUCCEDENT, 0),
                        null}
        };
    }

    public Object [][] parametersForGenericRuleTestMakeException() {
        return new Object[][] {
                {new OrLeftRule(), "b1 || b2 |- b1", new TermSelector(TermSelector.SequentPolarity.SUCCEDENT, 0),
                        null}
        };
    }

    public Object [][] parametersForGenericRuleTestConsiderException() {
        return new Object[][] {
                {}
        };
    }

    @Before
    public void setup() {
        symbolTable = new BuiltinSymbols();
        symbolTable.addFunctionSymbol(new FunctionSymbol("b1", Sort.BOOL));
        symbolTable.addFunctionSymbol(new FunctionSymbol("b2", Sort.BOOL));
        symbolTable.addFunctionSymbol(new FunctionSymbol("b3", Sort.BOOL));
        symbolTable.addFunctionSymbol(new FunctionSymbol("b4", Sort.BOOL));
        symbolTable.addFunctionSymbol(new FunctionSymbol("i1", Sort.INT));
        symbolTable.addFunctionSymbol(new FunctionSymbol("i2", Sort.INT));
        symbolTable.addFunctionSymbol(new FunctionSymbol("i3", Sort.INT));
        symbolTable.addFunctionSymbol(new FunctionSymbol("i4", Sort.INT));
    }


    /**
     *
     * Generic test for rules. Tests expects the rules to be applicable and not throw any exceptions.
     *
     * @param pr the rule to be tested
     * @param input sequent on which the rule is tested
     * @param ts a TermSelector pointing to the selected term (used as on-paramter)
     * @param results a list of resulting sequences given as strings (the size of results has to match the number of
     *                branches created by the rule application and each branch has to be contained in results)
     * @param usedVars optional: New function symbols (Pair<String, Sort>(name, Sort)), if null this defaults to the
     *                 preinitialized ones: boolean variables b1,...,b4, int variables i1,...,i4
     * @throws DafnyParserException
     * @throws RuleException
     */
    @Test
    @junitparams.Parameters
    public void genericRuleTestApplicable(ProofRule pr, String input, TermSelector ts,
                                List<String> results, Pair<String, Sort>... usedVars)
            throws DafnyParserException, RuleException, TermBuildException {
        Sequent s = null;
        if(usedVars == null) {
            s = parseSequent(input);
        } else {
            s = parseSequent(input, usedVars);
        }

        ProofNode pn = ProofMockUtil.mockProofNode(null, s.getAntecedent(), s.getSuccedent());

        Parameters params = new Parameters();
        params.putValue("on", ts.selectSubterm(s));

        ProofRuleApplication pra = pr.considerApplication(pn, s, ts);
        assertEquals(pra.getApplicability(), ProofRuleApplication.Applicability.APPLICABLE);
        assertEquals(pra.getScriptTranscript(), pr.getName() + " on='" + params.getValue("on") + "';");

        pra = pr.makeApplication(pn, params);
        List<ProofNode> newNodes = RuleApplicator.applyRule(pra, pn);

        assertEquals(newNodes.size(), results.size());

        for (int i = 0; i < newNodes.size(); ++i) {
            //assertTrue(results.contains(newNodes.get(i).getSequent().toString()));
            assertEquals(results.get(i), newNodes.get(i).getSequent().toString());
        }
    }


    /**
     * This test considers the applicable but excepts it to be not applicable.
     *
     * @param pr the rule to be tested
     * @param input sequent on which the rule is tested
     * @param ts a TermSelector pointing to the selected term (used as on-paramter)
     * @param usedVars optional: New function symbols (Pair<String, Sort>(name, Sort)), if null this defaults to the
     *                 preinitialized ones: boolean variables b1,...,b4, int variables i1,...,i4
     * @throws DafnyParserException
     * @throws RuleException
     */
    @Test
    @junitparams.Parameters
    public void genericRuleTestNotApplicable(ProofRule pr, String input, TermSelector ts,
                                          Pair<String, Sort>... usedVars)
            throws DafnyParserException, RuleException, TermBuildException {
        Sequent s;
        if(usedVars == null) {
            s = parseSequent(input);
        } else {
            s = parseSequent(input, usedVars);
        }

        ProofNode pn = ProofMockUtil.mockProofNode(null, s.getAntecedent(), s.getSuccedent());

        ProofRuleApplication pra = pr.considerApplication(pn, s, ts);
        assertEquals(pra.getApplicability(), ProofRuleApplication.Applicability.NOT_APPLICABLE);
    }

    /**
     * This test makes the applicable but excepts it to throw a  {@link RuleException}
     *
     * @param pr the rule to be tested
     * @param input sequent on which the rule is tested
     * @param ts a TermSelector pointing to the selected term (used as on-paramter)
     * @param usedVars optional: New function symbols (Pair<String, Sort>(name, Sort)), if null this defaults to the
     *                 preinitialized ones: boolean variables b1,...,b4, int variables i1,...,i4
     * @throws DafnyParserException
     * @throws RuleException
     */
    @Test(expected = RuleException.class)
    @junitparams.Parameters
    public void genericRuleTestMakeException(ProofRule pr, String input, TermSelector ts,
                                             Pair<String, Sort>... usedVars)
            throws DafnyParserException, RuleException, TermBuildException {
        Sequent s;
        if(usedVars == null) {
            s = parseSequent(input);
        } else {
            s = parseSequent(input, usedVars);
        }

        ProofNode pn = ProofMockUtil.mockProofNode(null, s.getAntecedent(), s.getSuccedent());

        Parameters params = new Parameters();
        params.putValue("on", ts.selectSubterm(s));

        ProofRuleApplication pra = pr.makeApplication(pn, params);
        RuleApplicator.applyRule(pra, pn);
    }

    public static Sequent parseSequent(String sequent, Pair<String, Sort>... usedVars) throws DafnyParserException {
        SymbolTable symbolTable = new BuiltinSymbols();
        for(Pair<String, Sort> p : usedVars) {
            symbolTable.addFunctionSymbol(new FunctionSymbol(p.getFst(), p.getSnd()));
        }
        TermParser tp = new TermParser(symbolTable);
        return tp.parseSequent(sequent);
    }

    private Sequent parseSequent(String sequent) throws DafnyParserException {
        TermParser tp = new TermParser(symbolTable);
        return tp.parseSequent(sequent);
    }
}
