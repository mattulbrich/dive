package edu.kit.iti.algover.rules;

import edu.kit.iti.algover.data.BuiltinSymbols;
import edu.kit.iti.algover.data.SymbolTable;
import edu.kit.iti.algover.parser.DafnyException;
import edu.kit.iti.algover.parser.DafnyParserException;
import edu.kit.iti.algover.proof.ProofFormula;
import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.rules.impl.CutRule;
import edu.kit.iti.algover.rules.impl.TrivialAndRight;
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
        TrivialAndRight rule = new TrivialAndRight();
        TermSelector selector = new TermSelector("A.0");
        TermParser tp = new TermParser(symbolTable);
        Sequent sequent = tp.parseSequent("i1 < i2 && i1 < i2 |- i1 < i2 && i1 < i2");
        Parameters params = new Parameters();
        params.putValue("on", new TermParameter(selector, sequent));
        assertEquals(1, params.entrySet().size());
        assertEquals("(... (?match: $and($lt(i1, i2), $lt(i1, i2))) ...) |-", ((TermParameter)params.getValue("on")).getSchematicTerm().toString());
        ProofRuleApplication app = rule.makeApplication(
                ProofMockUtil.mockProofNode(null, sequent.getAntecedent(), sequent.getSuccedent()),
                params
        );
        assertEquals(1, params.entrySet().size());
        assertEquals("(... (?match: $and($lt(i1, i2), $lt(i1, i2))) ...) |-", ((TermParameter)params.getValue("on")).getSchematicTerm().toString());
    }

    @Test(expected = RuleException.class)
    public void getUniqueMatchingParameterTest1()
            throws FormatException, TermBuildException, RuleException, DafnyParserException, DafnyException {
        TrivialAndRight rule = new TrivialAndRight();
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
        t = new SchemaCaptureTerm("?match", t);
        t = new SchemaOccurTerm(t);
        Sequent schemaSeq = new Sequent(Collections.singletonList(new ProofFormula(t)), Collections.emptyList());

        params.putValue("on", new TermParameter(schemaSeq, sequent));
        rule.considerApplication(
                ProofMockUtil.mockProofNode(null, sequent.getAntecedent(), sequent.getSuccedent()),
                params
        );
    }

    @Test
    public void getUniqueMatchingParameterTest2()
            throws FormatException, TermBuildException, RuleException, DafnyParserException, DafnyException {
        CutRule rule = new CutRule();
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
                new SchemaCaptureTerm("?match", t)
        );
        t = new SchemaOccurTerm(t);
        Sequent schemaSeq = new Sequent(Collections.singletonList(new ProofFormula(t)), Collections.emptyList());

        params.putValue("with", new TermParameter(schemaSeq, sequent));
        rule.considerApplication(
                ProofMockUtil.mockProofNode(null, sequent.getAntecedent(), sequent.getSuccedent()),
                params
        );
        assertEquals(1, params.entrySet().size());
        assertEquals("$lt(i1, i2)", ((TermParameter)params.getValue("with")).getTerm().toString());
    }

    @Test
    public void getUniqueMatchingParameterTest3()
            throws FormatException, TermBuildException, RuleException, DafnyParserException, DafnyException {
        TrivialAndRight rule = new TrivialAndRight();
        TermSelector selector = new TermSelector("A.0.0");
        TermParser tp = new TermParser(symbolTable);
        Sequent sequent = tp.parseSequent("i1 < i2 && i3 < i4 |- i1 < i2");
        Parameters params = new Parameters();
        params.putValue("on", new TermParameter(selector, sequent));
        assertEquals(1, params.entrySet().size());
        assertEquals("(... (?match: $lt(i1, i2)) ...) |-", ((TermParameter)params.getValue("on")).getSchematicTerm().toString());
        rule.considerApplication(
                ProofMockUtil.mockProofNode(null, sequent.getAntecedent(), sequent.getSuccedent()),
                params
        );
        assertEquals(1, params.entrySet().size());
        assertEquals("$lt(i1, i2)", ((TermParameter)params.getValue("on")).getTerm().toString());
    }
}
