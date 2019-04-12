package edu.kit.iti.algover.rules.impl;

import edu.kit.iti.algover.data.BuiltinSymbols;
import edu.kit.iti.algover.data.SymbolTable;
import edu.kit.iti.algover.parser.DafnyException;
import edu.kit.iti.algover.parser.DafnyParserException;
import edu.kit.iti.algover.project.Project;
import edu.kit.iti.algover.proof.Proof;
import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.rules.*;
import edu.kit.iti.algover.term.ApplTerm;
import edu.kit.iti.algover.term.FunctionSymbol;
import edu.kit.iti.algover.term.Sequent;
import edu.kit.iti.algover.term.Sort;
import edu.kit.iti.algover.term.builder.TermBuildException;
import edu.kit.iti.algover.term.parser.TermParser;
import edu.kit.iti.algover.util.FormatException;
import edu.kit.iti.algover.util.ProofMockUtil;
import edu.kit.iti.algover.util.TestUtil;
import org.antlr.runtime.RecognitionException;
import org.junit.Before;
import org.junit.Test;

import java.io.IOException;
import java.util.List;

import static org.junit.Assert.assertEquals;

public class ExhaustiveRuleTest {

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
    public void testStandard() throws DafnyParserException, DafnyException, FormatException, RuleException, IOException, RecognitionException {
        TermParser tp = new TermParser(symbolTable);
        String sequentString = "|- b1 && b2 && b3";
        Project project = TestUtil.mockProject("");
        Sequent s = tp.parseSequent(sequentString);
        Proof proof = ProofMockUtil.makeProofWithRoot(symbolTable, s);
        ExhaustiveRule rule = new ExhaustiveRule();
        Parameters params = new Parameters();
        params.putValue("ruleName", "andRight");
        params.putValue("on", new TermParameter(new TermSelector("S.0"), s));
        ProofRuleApplication pra = rule.makeApplication(proof.getProofRoot(), params);
        List<ProofNode> newNodes = RuleApplicator.applyRule(pra, proof.getProofRoot());
        assertEquals(1, newNodes.size());
        assertEquals(2, newNodes.get(0).getChildren().size());
        assertEquals(2, newNodes.get(0).getChildren().get(0).getChildren().size());
        assertEquals(0, newNodes.get(0).getChildren().get(1).getChildren().size());
    }
}
