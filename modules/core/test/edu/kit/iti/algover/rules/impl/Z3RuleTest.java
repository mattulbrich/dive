package edu.kit.iti.algover.rules.impl;

import edu.kit.iti.algover.dafnystructures.DafnyDecl;
import edu.kit.iti.algover.dafnystructures.DafnyMethod;
import edu.kit.iti.algover.dafnystructures.DafnyMethodBuilder;
import edu.kit.iti.algover.data.BuiltinSymbols;
import edu.kit.iti.algover.data.SymbolTable;
import edu.kit.iti.algover.parser.DafnyException;
import edu.kit.iti.algover.parser.DafnyParserException;
import edu.kit.iti.algover.parser.DafnyTree;
import edu.kit.iti.algover.parser.ParserTest;
import edu.kit.iti.algover.project.Project;
import edu.kit.iti.algover.proof.*;
import edu.kit.iti.algover.rules.*;
import edu.kit.iti.algover.term.FunctionSymbol;
import edu.kit.iti.algover.term.Sequent;
import edu.kit.iti.algover.term.Sort;
import edu.kit.iti.algover.term.builder.TermBuildException;
import edu.kit.iti.algover.term.parser.TermParser;
import edu.kit.iti.algover.util.Pair;
import edu.kit.iti.algover.util.ProofMockUtil;
import edu.kit.iti.algover.util.TestUtil;
import org.antlr.runtime.RecognitionException;
import org.junit.Before;
import org.junit.Test;

import java.io.ByteArrayInputStream;
import java.io.IOException;
import java.util.List;

import static org.junit.Assert.assertEquals;

public class Z3RuleTest {
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
    public void basicTest() throws DafnyParserException, DafnyException, TermBuildException, RuleException, IOException, RecognitionException {
        MockPVCBuilder builder = new MockPVCBuilder();
        builder.setSymbolTable(symbolTable);
        Project mock = TestUtil.mockProject("method m() ensures true {}");
        Sequent s = null;
        String input = "b1 |- b1";
        s = parseSequent(input);
        builder.setSequent(s);
        builder.setDeclaration(mock.getMethod("m"));
        PVC pvc = builder.build();

        ProofNode pn = ProofMockUtil.mockProofNode(null, s.getAntecedent(), s.getSuccedent(), pvc);
        ProofRule pr = new Z3Rule();

        ProofRuleApplication pra = pr.makeApplication(pn, new Parameters());

        assertEquals(pra.getApplicability(), ProofRuleApplication.Applicability.APPLICABLE);
    }

    private Sequent parseSequent(String sequent) throws DafnyParserException, DafnyException {
        TermParser tp = new TermParser(symbolTable);
        return tp.parseSequent(sequent);
    }
}
