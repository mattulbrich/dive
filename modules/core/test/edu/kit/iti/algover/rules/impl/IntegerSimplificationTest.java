package edu.kit.iti.algover.rules.impl;

import edu.kit.iti.algover.data.BuiltinSymbols;
import edu.kit.iti.algover.data.SymbolTable;
import edu.kit.iti.algover.parser.DafnyException;
import edu.kit.iti.algover.parser.DafnyParserException;
import edu.kit.iti.algover.project.Project;
import edu.kit.iti.algover.proof.Proof;
import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.rules.Parameters;
import edu.kit.iti.algover.rules.ProofRuleApplication;
import edu.kit.iti.algover.rules.RuleApplicator;
import edu.kit.iti.algover.rules.RuleException;
import edu.kit.iti.algover.rules.TermParameter;
import edu.kit.iti.algover.rules.TermSelector;
import edu.kit.iti.algover.term.FunctionSymbol;
import edu.kit.iti.algover.term.Sequent;
import edu.kit.iti.algover.term.Sort;
import edu.kit.iti.algover.term.builder.TermBuildException;
import edu.kit.iti.algover.term.parser.TermParser;
import edu.kit.iti.algover.util.FormatException;
import edu.kit.iti.algover.util.ProofMockUtil;
import edu.kit.iti.algover.util.TestUtil;
import org.junit.Before;
import org.junit.Test;

import java.io.IOException;
import java.util.List;

import static org.junit.Assert.assertEquals;

/**
 * Created by jklamroth on 11/7/18.
 */
public class IntegerSimplificationTest {
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
        symbolTable.addFunctionSymbol(new FunctionSymbol("skvar0", Sort.INT));
    }

    @Test
    public void testAddZero() throws DafnyParserException, DafnyException, TermBuildException, FormatException, RuleException, IOException, org.antlr.runtime.RecognitionException {
        TermParser tp = new TermParser(symbolTable);
        String sequentString = "i1 + 0 > 0 |-";
        Sequent s = tp.parseSequent(sequentString);
        Proof p = ProofMockUtil.makeProofWithRoot(symbolTable, s);
        Project project = TestUtil.emptyProject();
        TestUtil.setField(p.getPVC(), "project", project);
        ProofNode pn = p.getProofRoot();
        IntegerSimplification rule = new IntegerSimplification();
        Parameters params = new Parameters();
        params.putValue("on", new TermParameter(new TermSelector("A.0.0"), s));
        ProofRuleApplication pra = rule.makeApplication(pn, params);
        List<ProofNode> newNodes = RuleApplicator.applyRule(pra, pn);
        assertEquals(1, newNodes.size());
        ProofNode res = newNodes.get(0);
        while(res.getChildren().size() > 0) {
            assertEquals(1, res.getChildren().size());
            res = res.getChildren().get(0);
        }

        assertEquals("$gt(i1, 0) |-", res.getSequent().toString());
    }

    @Test
    public void testTimesOne() throws DafnyParserException, DafnyException, TermBuildException, FormatException, RuleException, IOException, org.antlr.runtime.RecognitionException {
        TermParser tp = new TermParser(symbolTable);
        String sequentString = "i1 * 1 > 0 |-";
        Sequent s = tp.parseSequent(sequentString);
        Proof p = ProofMockUtil.makeProofWithRoot(symbolTable, s);
        Project project = TestUtil.emptyProject();
        TestUtil.setField(p.getPVC(), "project", project);
        ProofNode pn = p.getProofRoot();
        IntegerSimplification rule = new IntegerSimplification();
        Parameters params = new Parameters();
        params.putValue("on", new TermParameter(new TermSelector("A.0.0"), s));
        ProofRuleApplication pra = rule.makeApplication(pn, params);
        List<ProofNode> newNodes = RuleApplicator.applyRule(pra, pn);
        assertEquals(1, newNodes.size());
        ProofNode res = newNodes.get(0);
        while(res.getChildren().size() > 0) {
            assertEquals(1, res.getChildren().size());
            res = res.getChildren().get(0);
        }

        assertEquals("$gt(i1, 0) |-", res.getSequent().toString());
    }

    @Test
    public void testMultiple() throws DafnyParserException, DafnyException, TermBuildException, FormatException, RuleException, IOException, org.antlr.runtime.RecognitionException {
        TermParser tp = new TermParser(symbolTable);
        String sequentString = "i1 + 0 + 0 * 1 > 0 |-";
        Sequent s = tp.parseSequent(sequentString);
        Proof p = ProofMockUtil.makeProofWithRoot(symbolTable, s);
        Project project = TestUtil.emptyProject();
        TestUtil.setField(p.getPVC(), "project", project);
        ProofNode pn = p.getProofRoot();
        IntegerSimplification rule = new IntegerSimplification();
        Parameters params = new Parameters();
        params.putValue("on", new TermParameter(new TermSelector("A.0.0"), s));
        ProofRuleApplication pra = rule.makeApplication(pn, params);
        List<ProofNode> newNodes = RuleApplicator.applyRule(pra, pn);
        assertEquals(1, newNodes.size());
        ProofNode res = newNodes.get(0);
        while(res.getChildren().size() > 0) {
            assertEquals(1, res.getChildren().size());
            res = res.getChildren().get(0);
        }

        assertEquals("$gt(i1, 0) |-", res.getSequent().toString());
    }

    @Test
    public void testMultiple2() throws DafnyParserException, DafnyException, TermBuildException, FormatException, RuleException, IOException, org.antlr.runtime.RecognitionException {
        TermParser tp = new TermParser(symbolTable);
        String sequentString = "i1 + 5 + 0 * 1 * 6 + 1 - 0 / 1 > 0 |-";
        Sequent s = tp.parseSequent(sequentString);
        Proof p = ProofMockUtil.makeProofWithRoot(symbolTable, s);
        Project project = TestUtil.emptyProject();
        TestUtil.setField(p.getPVC(), "project", project);
        ProofNode pn = p.getProofRoot();
        IntegerSimplification rule = new IntegerSimplification();
        Parameters params = new Parameters();
        params.putValue("on", new TermParameter(new TermSelector("A.0.0"), s));
        ProofRuleApplication pra = rule.makeApplication(pn, params);
        List<ProofNode> newNodes = RuleApplicator.applyRule(pra, pn);
        assertEquals(1, newNodes.size());
        ProofNode res = newNodes.get(0);
        while(res.getChildren().size() > 0) {
            assertEquals(1, res.getChildren().size());
            res = res.getChildren().get(0);
        }

        assertEquals("$gt($plus($plus(i1, 5), 1), 0) |-", res.getSequent().toString());
    }
}
