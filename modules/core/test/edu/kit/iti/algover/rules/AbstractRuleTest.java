/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.rules;

import edu.kit.iti.algover.data.BuiltinSymbols;
import edu.kit.iti.algover.data.SymbolTable;
import edu.kit.iti.algover.parser.DafnyException;
import edu.kit.iti.algover.parser.DafnyParserException;
import edu.kit.iti.algover.proof.ProofFormula;
import edu.kit.iti.algover.rules.impl.AddHypothesisRule;
import edu.kit.iti.algover.rules.impl.AndRightRule;
import edu.kit.iti.algover.term.*;
import edu.kit.iti.algover.term.builder.TermBuildException;
import edu.kit.iti.algover.term.parser.TermParser;
import edu.kit.iti.algover.util.FormatException;
import edu.kit.iti.algover.util.ProofMockUtil;
import org.junit.Before;
import org.junit.Test;

import java.util.Collections;

import static org.junit.Assert.assertEquals;

/**
 * Created by jklamroth on 6/19/18.
 */
public class AbstractRuleTest {
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
    public void getUniqueMatchingParameterTest()
            throws FormatException, TermBuildException, RuleException, DafnyParserException, DafnyException {
        AndRightRule rule = new AndRightRule();
        TermSelector selector = new TermSelector("S.0");
        TermParser tp = new TermParser(symbolTable);
        Sequent sequent = tp.parseSequent("i1 < i2 && i1 < i2 |- i1 < i2 && i1 < i2");
        Parameters params = new Parameters();
        params.putValue(DefaultFocusProofRule.ON_PARAM_OPT, new TermParameter(selector, sequent));
        assertEquals(1, params.entrySet().size());
        assertEquals("|- _", ((TermParameter)params.getValue(DefaultFocusProofRule.ON_PARAM_OPT)).getMatchParameter().toString());
        ProofRuleApplication app = rule.makeApplication(
                ProofMockUtil.mockProofNode(null, sequent.getAntecedent(), sequent.getSuccedent()),
                params
        );
        assertEquals(1, params.entrySet().size());
        assertEquals("|- _", ((TermParameter)params.getValue(DefaultFocusProofRule.ON_PARAM_OPT)).getMatchParameter().toString());
    }

    @Test(expected = RuleException.class)
    public void getUniqueMatchingParameterTest1()
            throws FormatException, TermBuildException, RuleException, DafnyParserException, DafnyException {
        AndRightRule rule = new AndRightRule();
        TermSelector selector = new TermSelector("A.0.0");
        TermParser tp = new TermParser(symbolTable);
        Sequent sequent = tp.parseSequent("i1 < i2 && i1 < i2 |- i1 < i2");
        Parameters params = new Parameters();
        Term t = new ApplTerm(BuiltinSymbols.LT,
                new ApplTerm(
                        new FunctionSymbol("i1", Sort.INT)),
                        new ApplTerm(new FunctionSymbol("i2", Sort.INT)
                        )
                );
        t = new SchemaCaptureTerm("?m", t);
        t = new SchemaOccurTerm(t);
        Sequent schemaSeq = new Sequent(Collections.singletonList(new ProofFormula(t)), Collections.emptyList());

        params.putValue(DefaultFocusProofRule.ON_PARAM_OPT, new TermParameter(schemaSeq, sequent));
        rule.makeApplication(
                ProofMockUtil.mockProofNode(null, sequent.getAntecedent(), sequent.getSuccedent()),
                params
        );
    }

    @Test
    public void getUniqueMatchingParameterTest2()
            throws FormatException, TermBuildException, RuleException, DafnyParserException, DafnyException {
        AddHypothesisRule rule = new AddHypothesisRule();
        TermSelector selector = new TermSelector("A.0.0");
        TermParser tp = new TermParser(symbolTable);
        Sequent sequent = tp.parseSequent("i1 < i2 && i1 < i2 |- i1 < i2");
        Parameters params = new Parameters();
        Term t = new ApplTerm(BuiltinSymbols.LT,
                new ApplTerm(
                        new FunctionSymbol("i1", Sort.INT)),
                new ApplTerm(new FunctionSymbol("i2", Sort.INT)
                )
        );
        t = new ApplTerm(BuiltinSymbols.AND,
                t,
                new SchemaCaptureTerm("?m", t)
        );
        t = new SchemaOccurTerm(t);
        Sequent schemaSeq = new Sequent(Collections.singletonList(new ProofFormula(t)), Collections.emptyList());

        params.putValue(AddHypothesisRule.WITH_PARAM, new TermParameter(schemaSeq, sequent));
        rule.makeApplication(
                ProofMockUtil.mockProofNode(null, sequent.getAntecedent(), sequent.getSuccedent()),
                params
        );
        assertEquals(1, params.entrySet().size());
        assertEquals("$lt(i1, i2)", ((TermParameter)params.getValue(AddHypothesisRule.WITH_PARAM)).getTerm().toString());
    }

    @Test(expected = NotApplicableException.class)
    public void getUniqueMatchingParameterTest3()
            throws FormatException, TermBuildException, RuleException, DafnyParserException, DafnyException {
        AndRightRule rule = new AndRightRule();
        TermSelector selector = new TermSelector("A.0.0");
        TermParser tp = new TermParser(symbolTable);
        Sequent sequent = tp.parseSequent("i1 < i2 && i3 < i4 |- i1 < i2");
        Parameters params = new Parameters();
        params.putValue(DefaultFocusProofRule.ON_PARAM_OPT, new TermParameter(selector, sequent));
        assertEquals(1, params.entrySet().size());
        assertEquals("$and(?m, _) |-", ((TermParameter)params.getValue(DefaultFocusProofRule.ON_PARAM_OPT)).getMatchParameter().toString());
        rule.makeApplication(ProofMockUtil.mockProofNode(null, sequent), params);
    }
}
