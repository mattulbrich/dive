package edu.kit.iti.algover.rules.impl;

import edu.kit.iti.algover.data.BuiltinSymbols;
import edu.kit.iti.algover.data.SymbolTable;
import edu.kit.iti.algover.parser.DafnyException;
import edu.kit.iti.algover.parser.DafnyParserException;
import edu.kit.iti.algover.proof.MockPVCBuilder;
import edu.kit.iti.algover.proof.Proof;
import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.rules.Parameters;
import edu.kit.iti.algover.rules.ProofRuleApplication;
import edu.kit.iti.algover.rules.RuleApplicator;
import edu.kit.iti.algover.rules.RuleException;
import edu.kit.iti.algover.rules.TermParameter;
import edu.kit.iti.algover.rules.TermSelector;
import edu.kit.iti.algover.term.ApplTerm;
import edu.kit.iti.algover.term.FunctionSymbol;
import edu.kit.iti.algover.term.Sequent;
import edu.kit.iti.algover.term.Sort;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.term.builder.TermBuildException;
import edu.kit.iti.algover.term.parser.TermParser;
import edu.kit.iti.algover.util.FormatException;
import edu.kit.iti.algover.util.ProofMockUtil;
import edu.kit.iti.algover.util.TestUtil;
import org.antlr.v4.runtime.RecognitionException;
import org.junit.Before;
import org.junit.Test;

import java.io.IOException;
import java.util.List;

import static org.junit.Assert.assertEquals;

/**
 * Created by jklamroth on 11/7/18.
 */
public class SkolemizationTest {
    SymbolTable symbolTable;

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

    @Test(expected = RuleException.class)
    public void testNested() throws DafnyParserException, DafnyException, TermBuildException, FormatException, RuleException, IOException, org.antlr.runtime.RecognitionException {
        TermParser tp = new TermParser(symbolTable);
        String sequentString = "(forall i1:int :: i1 >= 0 && i1 < 5 ==> (exists i2:int :: i2 >= 0 && i2 < 5 ==> i1 == i2)) |-";
        Sequent s = tp.parseSequent(sequentString);
        Proof p = ProofMockUtil.makeProofWithRoot(symbolTable, s);
        ProofNode pn = p.getProofRoot();
        SkolemizationRule rule = new SkolemizationRule();
        Parameters params = new Parameters();
        params.putValue("on", new TermParameter(new TermSelector("A.0"), s));
        ProofRuleApplication pra = rule.makeApplication(pn, params);
        List<ProofNode> newNodes = RuleApplicator.applyRule(pra, pn);
    }

    @Test
    public void testSingle() throws DafnyParserException, DafnyException, TermBuildException, FormatException, RuleException, IOException, org.antlr.runtime.RecognitionException {
        TermParser tp = new TermParser(symbolTable);
        String sequentString = "(exists i2:int :: i2 >= 0 && i2 < 5 ==> 3 == i2) |-";
        Sequent s = tp.parseSequent(sequentString);
        Proof p = ProofMockUtil.makeProofWithRoot(symbolTable, s);
        ProofNode pn = p.getProofRoot();
        SkolemizationRule rule = new SkolemizationRule();
        Parameters params = new Parameters();
        params.putValue("on", new TermParameter(new TermSelector("A.0"), s));
        ProofRuleApplication pra = rule.makeApplication(pn, params);
        List<ProofNode> newNodes = RuleApplicator.applyRule(pra, pn);
        assertEquals(1, newNodes.size());
        assertEquals("$imp($and($ge(skvar0, 0), $lt(skvar0, 5)), $eq<int>(3, skvar0)) |-", newNodes.get(0).getSequent().toString());
    }

    @Test
    public void testExistingVar() throws DafnyParserException, DafnyException, TermBuildException, FormatException, RuleException, IOException, org.antlr.runtime.RecognitionException {
        symbolTable.addFunctionSymbol(new FunctionSymbol("skvar0", Sort.INT));
        TermParser tp = new TermParser(symbolTable);
        String sequentString = "(exists i2:int :: i2 >= 0 && i2 < 5 ==> skvar0 == i2) |-";
        Sequent s = tp.parseSequent(sequentString);
        Proof p = ProofMockUtil.makeProofWithRoot(symbolTable, s);
        ProofNode pn = p.getProofRoot();
        SkolemizationRule rule = new SkolemizationRule();
        Parameters params = new Parameters();
        params.putValue("on", new TermParameter(new TermSelector("A.0"), s));
        ProofRuleApplication pra = rule.makeApplication(pn, params);
        List<ProofNode> newNodes = RuleApplicator.applyRule(pra, pn);
        assertEquals(1, newNodes.size());
        assertEquals("$imp($and($ge(skvar1, 0), $lt(skvar1, 5)), $eq<int>(skvar0, skvar1)) |-", newNodes.get(0).getSequent().toString());
    }
}
