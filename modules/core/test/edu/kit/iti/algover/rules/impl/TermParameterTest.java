package edu.kit.iti.algover.rules.impl;

import edu.kit.iti.algover.data.BuiltinSymbols;
import edu.kit.iti.algover.data.SymbolTable;
import edu.kit.iti.algover.parser.DafnyException;
import edu.kit.iti.algover.parser.DafnyParserException;
import edu.kit.iti.algover.rules.RuleException;
import edu.kit.iti.algover.rules.TermParameter;
import edu.kit.iti.algover.rules.TermSelector;
import edu.kit.iti.algover.term.FunctionSymbol;
import edu.kit.iti.algover.term.Sequent;
import edu.kit.iti.algover.term.Sort;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.term.builder.TermBuildException;
import edu.kit.iti.algover.term.parser.TermParser;
import edu.kit.iti.algover.util.FormatException;
import org.junit.Before;
import org.junit.Test;

import static org.junit.Assert.assertEquals;

/**
 * Created by jklamroth on 9/13/18.
 */
public class TermParameterTest {
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
    public void TsToTest()
            throws FormatException, TermBuildException, RuleException, DafnyParserException, DafnyException {
        TermSelector selector = new TermSelector("A.0");
        TermParser tp = new TermParser(symbolTable);
        Sequent sequent = tp.parseSequent("i1 < i2 && i1 < i2 |- i1 < i2 && i1 < i2");
        TermParameter p = new TermParameter(selector, sequent);
        assertEquals("(... (?match: $and($lt(i1, i2), $lt(i1, i2))) ...) |-", p.getSchematicSequent().toString());
        assertEquals("$and($lt(i1, i2), $lt(i1, i2))", p.getTerm().toString());
    }

    @Test
    public void TermToTest() throws FormatException, TermBuildException, RuleException, DafnyParserException, DafnyException {
        TermParser tp = new TermParser(symbolTable);
        Term term = tp.parse("i1 < i2");
        Sequent sequent = tp.parseSequent("i1 < i2 |- i1 + i2");
        TermParameter parameter = new TermParameter(term, sequent);
        assertEquals(new TermSelector("A.0"), parameter.getTermSelector());
        assertEquals("(... (?match: $lt(i1, i2)) ...) |-", parameter.getSchematicSequent().toString());
    }

    @Test(expected = RuleException.class)
    public void TermToTest2() throws FormatException, TermBuildException, RuleException, DafnyParserException, DafnyException {
        TermParser tp = new TermParser(symbolTable);
        Term term = tp.parse("i1 < i2");
        Sequent sequent = tp.parseSequent("i1 < i2 |- i1 < i2");
        TermParameter parameter = new TermParameter(term, sequent);
        parameter.getTermSelector();
    }


    @Test
    public void SchematicToTest() throws FormatException, TermBuildException, RuleException, DafnyParserException, DafnyException {
        TermParser tp = new TermParser(symbolTable);
        tp.setSchemaMode(true);
        Sequent schematic = tp.parseSequent("(... (?match: $lt(i1, i2)) ...) |-");
        Sequent sequent = tp.parseSequent("i1 < i2 |- i1 < i2");
        TermParameter parameter = new TermParameter(schematic, sequent);
        assertEquals(new TermSelector("A.0"), parameter.getTermSelector());
        assertEquals("$lt(i1, i2)", parameter.getTerm().toString());
    }

    @Test(expected = RuleException.class)
    public void SchematicToTest2() throws FormatException, TermBuildException, RuleException, DafnyParserException, DafnyException {
        TermParser tp = new TermParser(symbolTable);
        tp.setSchemaMode(true);
        Sequent schematic = tp.parseSequent("(... $lt(i1, i2) ...) |-");
        Sequent sequent = tp.parseSequent("i1 < i2 |- i1 < i2");
        TermParameter parameter = new TermParameter(schematic, sequent);
        parameter.getTermSelector();
    }

    @Test(expected = RuleException.class)
    public void SchematicTermToSequentTest() throws FormatException, TermBuildException, RuleException, DafnyParserException, DafnyException {
        TermParser tp = new TermParser(symbolTable);
        tp.setSchemaMode(true);
        Term schematic = tp.parse("_ < _");
        Sequent sequent = tp.parseSequent("i1 < i2 |- i1 < i2");
        TermParameter parameter = new TermParameter(schematic, sequent);
        parameter.getTermSelector();
    }

    @Test
    public void SchematicTermToSequentTest2() throws FormatException, TermBuildException, RuleException, DafnyParserException, DafnyException {
        TermParser tp = new TermParser(symbolTable);
        tp.setSchemaMode(true);
        Term schematic = tp.parse("_ < _");
        Sequent sequent = tp.parseSequent("i1 < i2 |- i1 + i2");
        TermParameter parameter = new TermParameter(schematic, sequent);
        assertEquals(new TermSelector("A.0"), parameter.getTermSelector());
        assertEquals("(... (?match: $lt(i1, i2)) ...) |-", parameter.getSchematicSequent().toString());
    }

    @Test
    public void SchematicTermToSequentTest3() throws FormatException, TermBuildException, RuleException, DafnyParserException, DafnyException {
        TermParser tp = new TermParser(symbolTable);
        tp.setSchemaMode(true);
        Term schematic = tp.parse("_ < (?match: _)");
        Sequent sequent = tp.parseSequent("i1 < i2 |- i1 + i2");
        TermParameter parameter = new TermParameter(schematic, sequent);
        assertEquals(new TermSelector("A.0.1"), parameter.getTermSelector());
        assertEquals("(... (?match: i2) ...) |-", parameter.getSchematicSequent().toString());
    }
}
