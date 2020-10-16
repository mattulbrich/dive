/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.rules.impl;

import edu.kit.iti.algover.data.BuiltinSymbols;
import edu.kit.iti.algover.data.SymbolTable;
import edu.kit.iti.algover.parser.DafnyException;
import edu.kit.iti.algover.parser.DafnyParserException;
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
import org.junit.Before;
import org.junit.Test;

import java.util.List;

import static org.junit.Assert.assertEquals;

/**
 * Created by jklamroth on 11/7/18.
 */
public class QuantifierInstatiationTest {
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

    @Test
    public void testStandard() throws DafnyParserException, DafnyException, TermBuildException, FormatException, RuleException {
        TermParser tp = new TermParser(symbolTable);
        String sequentString = "(forall i1:int :: i1 >= 0 && i1 < 1 ==> i1 == 0) |-";
        Sequent s = tp.parseSequent(sequentString);
        ProofNode pn = ProofMockUtil.mockProofNode(null, s);
        QuantifierInstantiation rule = new QuantifierInstantiation();
        Parameters params = new Parameters();
        params.putValue(rule.getOnParameter(), new TermParameter(new TermSelector("A.0"), s));
        params.putValue(QuantifierInstantiation.WITH_PARAM, new TermParameter(new ApplTerm(new FunctionSymbol("0", Sort.INT)), null));
        ProofRuleApplication pra = rule.makeApplication(pn, params);
        List<ProofNode> newNodes = RuleApplicator.applyRule(pra, null, pn);
        assertEquals(1, newNodes.size());
        assertEquals("$imp($and($ge(0, 0), $lt(0, 1)), $eq<int>(0, 0)) |-", newNodes.get(0).getSequent().toString());
    }

    @Test
    public void testEmpty() throws DafnyParserException, DafnyException, TermBuildException, FormatException, RuleException {
        TermParser tp = new TermParser(symbolTable);
        String sequentString = "(forall i2:int :: i1 >= 0 && i1 < 1 ==> i1 == 0) |-";
        Sequent s = tp.parseSequent(sequentString);
        ProofNode pn = ProofMockUtil.mockProofNode(null, s);
        QuantifierInstantiation rule = new QuantifierInstantiation();
        Parameters params = new Parameters();
        params.putValue(rule.getOnParameter(), new TermParameter(new TermSelector("A.0"), s));
        params.putValue(QuantifierInstantiation.WITH_PARAM, new TermParameter(new ApplTerm(new FunctionSymbol("0", Sort.INT)), null));
        ProofRuleApplication pra = rule.makeApplication(pn, params);
        List<ProofNode> newNodes = RuleApplicator.applyRule(pra, null, pn);
        assertEquals(1, newNodes.size());
        assertEquals("$imp($and($ge(i1, 0), $lt(i1, 1)), $eq<int>(i1, 0)) |-", newNodes.get(0).getSequent().toString());
    }

    @Test
    public void testNotAll() throws DafnyParserException, DafnyException, TermBuildException, FormatException, RuleException {
        TermParser tp = new TermParser(symbolTable);
        String sequentString = "(forall i2:int :: i2 >= 0 && i3 < 1 ==> i1 == 0) |-";
        Sequent s = tp.parseSequent(sequentString);
        ProofNode pn = ProofMockUtil.mockProofNode(null, s);
        QuantifierInstantiation rule = new QuantifierInstantiation();
        Parameters params = new Parameters();
        params.putValue(rule.getOnParameter(), new TermParameter(new TermSelector("A.0"), s));
        params.putValue(QuantifierInstantiation.WITH_PARAM, new TermParameter(new ApplTerm(new FunctionSymbol("0", Sort.INT)), null));
        ProofRuleApplication pra = rule.makeApplication(pn, params);
        List<ProofNode> newNodes = RuleApplicator.applyRule(pra, null, pn);
        assertEquals(1, newNodes.size());
        assertEquals("$imp($and($ge(0, 0), $lt(i3, 1)), $eq<int>(i1, 0)) |-", newNodes.get(0).getSequent().toString());
    }

    @Test
    public void testReplaceComplicated() throws DafnyParserException, DafnyException, TermBuildException, FormatException, RuleException {
        TermParser tp = new TermParser(symbolTable);
        String sequentString = "(forall i2:int :: i2 >= 0 && i3 < 1 ==> i1 == 0) |-";
        Sequent s = tp.parseSequent(sequentString);
        ProofNode pn = ProofMockUtil.mockProofNode(null, s);
        QuantifierInstantiation rule = new QuantifierInstantiation();
        Parameters params = new Parameters();
        params.putValue(rule.getOnParameter(), new TermParameter(new TermSelector("A.0"), s));
        Term rt = tp.parse("i1 + i1 % i3 - i4");
        params.putValue(QuantifierInstantiation.WITH_PARAM, new TermParameter(rt, null));
        ProofRuleApplication pra = rule.makeApplication(pn, params);
        List<ProofNode> newNodes = RuleApplicator.applyRule(pra, null, pn);
        assertEquals(1, newNodes.size());
        assertEquals("$imp($and($ge($minus($plus(i1, $modulo(i1, i3)), i4), 0), $lt(i3, 1)), $eq<int>(i1, 0)) |-", newNodes.get(0).getSequent().toString());
    }

    @Test(expected = RuleException.class)
    public void testReplaceWithContainedVar() throws DafnyParserException, DafnyException, TermBuildException, FormatException, RuleException {
        TermParser tp = new TermParser(symbolTable);
        String sequentString = "(forall i2:int :: i2 >= 0 && i3 < 1 ==> i1 == 0), exists y :: y==42 |-";
        Sequent s = tp.parseSequent(sequentString);
        ProofNode pn = ProofMockUtil.mockProofNode(null, s);
        QuantifierInstantiation rule = new QuantifierInstantiation();
        Parameters params = new Parameters();
        params.putValue(rule.getOnParameter(), new TermParameter(new TermSelector("A.0"), s));
        tp.setSchemaMode(true);
        Term rt = tp.parse("... (?match:_) == 42 ...");
        params.putValue(QuantifierInstantiation.WITH_PARAM, new TermParameter(rt, s));
        ProofRuleApplication pra = rule.makeApplication(pn, params);
    }
}
