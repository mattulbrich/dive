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
import edu.kit.iti.algover.rules.RuleException;
import edu.kit.iti.algover.rules.TermParameter;
import edu.kit.iti.algover.rules.TermSelector;
import edu.kit.iti.algover.rules.TermSelector.SequentPolarity;
import edu.kit.iti.algover.term.FunctionSymbol;
import edu.kit.iti.algover.term.Sequent;
import edu.kit.iti.algover.term.Sort;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.term.builder.TermBuildException;
import edu.kit.iti.algover.term.parser.TermParser;
import edu.kit.iti.algover.util.FormatException;
import junitparams.JUnitParamsRunner;
import junitparams.Parameters;
import org.junit.Before;
import org.junit.Test;
import org.junit.runner.RunWith;

import static org.junit.Assert.assertEquals;

/**
 * Created by jklamroth on 9/13/18.
 */
@RunWith(JUnitParamsRunner.class)
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
        symbolTable.addFunctionSymbol(new FunctionSymbol("$$a", Sort.INT, Sort.HEAP, Sort.INT));
    }

    public String[][] parametersForTsToTest() {
        return new String[][] {
                { "A.0", "i1 < i2 && i1 < i2 |- i1 < i2 && i1 < i2", "_ |-" },
                { "A.0.0", "i1 < i2 && i1 < i2 |- i1 < i2 && i1 < i2", "?m && _ |-" },
                { "A.0.1", "i1 < i2 && i1 < i2 |- i1 < i2 && i1 < i2", "_ && ?m |-" },
                { "S.0", "i1 < i2 && i1 < i2 |- i1 < i2 && i1 < i2", "|- _" },
                //{ "A.0.0.0", "1+2 > 1 |-", "?m+2" }, //are you sure we actually support this in the matcher?
                { "A.0.0.1", "1+2 > 1 |-", "2" },
        };
    }

    @Test @Parameters
    public void TsToTest(String termSelStr, String seqStr, String expected) throws Exception {
        TermSelector selector = new TermSelector(termSelStr);
        TermParser tp = new TermParser(symbolTable);
        Sequent sequent = tp.parseSequent(seqStr);
        TermParameter p = new TermParameter(selector, sequent);
        tp.setSchemaMode(true);
        String expectedStr = tp.parseTermOrSequent(expected).toString();
        assertEquals(expectedStr, p.getMatchParameter().toString());
        assertEquals(selector, p.getTermSelector());
    }

    @Test
    public void TermToTest() throws FormatException, TermBuildException, RuleException, DafnyParserException, DafnyException {
        TermParser tp = new TermParser(symbolTable);
        Term term = tp.parse("i1 < i2");
        Sequent sequent = tp.parseSequent("i1 < i2 |- i1 + i2 > 0");
        TermParameter parameter = new TermParameter(term, sequent);
        assertEquals(new TermSelector("A.0"), parameter.getTermSelector());
        assertEquals("_ |-", parameter.getMatchParameter().toString());
        assertEquals(term, parameter.getTerm());
    }

    @Test
    public void EllipsisTest() throws DafnyParserException, DafnyException, FormatException, RuleException {
        TermParser tp = new TermParser(symbolTable);
        tp.setSchemaMode(true);
        Sequent sequent = tp.parseSequent("i1 < i2 |- i1 + i2 > 0");
        TermParameter parameter = new TermParameter(new TermSelector("A.0"), sequent);
        assertEquals(new TermSelector("A.0"), parameter.getTermSelector());
        assertEquals("_ |-", parameter.getMatchParameter().toString());
    }

    @Test
    public void EllipsisTest2() throws DafnyParserException, DafnyException, FormatException, RuleException {
        TermParser tp = new TermParser(symbolTable);
        tp.setSchemaMode(true);
        Sequent sequent = tp.parseSequent("i1 < i2, b1 |- i1 + i2 > 0");
        TermParameter parameter = new TermParameter(new TermSelector("A.0"), sequent);
        assertEquals(new TermSelector("A.0"), parameter.getTermSelector());
        assertEquals("$lt(_, _) |-", parameter.getMatchParameter().toString());
    }

    @Test
    public void EllipsisTest3() throws DafnyParserException, DafnyException, FormatException, RuleException {
        TermParser tp = new TermParser(symbolTable);
        tp.setSchemaMode(true);
        Sequent sequent = tp.parseSequent("i1 < i2, b1 |- i1 + i2 > 0");
        TermParameter parameter = new TermParameter(new TermSelector("S.0.0"), sequent);
        assertEquals(new TermSelector("S.0.0"), parameter.getTermSelector());
        assertEquals("|- $gt(?m, _)", parameter.getMatchParameter().toString());
    }


    @Test
    public void EllipsisTest4() throws DafnyParserException, DafnyException, FormatException, RuleException {
        TermParser tp = new TermParser(symbolTable);
        tp.setSchemaMode(true);
        Sequent sequent = tp.parseSequent("let i1 := i2 :: (let i2 := i3 :: (i1 < i2)), let i1 := i2 :: (let i2 := i3 :: (i2 > i3)), b1 |- i1 + i2 > 0");
        TermParameter parameter = new TermParameter(new TermSelector("A.0"), sequent);
        assertEquals(new TermSelector("A.0"), parameter.getTermSelector());
        assertEquals("(let i1 := i2 :: (... $lt(i1, i2) ...)) |-", parameter.getMatchParameter().toString());
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
        Sequent schematic = tp.parseSequent("(... (?m: $lt(i1, i2)) ...) |-");
        Sequent sequent = tp.parseSequent("i1 < i2 |- i1 < i2");
        TermParameter parameter = new TermParameter(schematic, sequent);
        assertEquals(new TermSelector("A.0"), parameter.getTermSelector());
        assertEquals("$lt(i1, i2)", parameter.getTerm().toString());
        assertEquals(schematic, parameter.getSchematicSequent());
    }

    @Test
    public void SchematicToTest2() throws FormatException, TermBuildException, RuleException, DafnyParserException, DafnyException {
        TermParser tp = new TermParser(symbolTable);
        tp.setSchemaMode(true);
        Sequent schematic = tp.parseSequent("(... $lt(i1, i2) ...) |-");
        Sequent sequent = tp.parseSequent("i1 < i2 |- i1 < i2");
        TermParameter parameter = new TermParameter(schematic, sequent);
        assertEquals(new TermSelector("A.0"), parameter.getTermSelector());
        assertEquals("$lt(i1, i2)", parameter.getTerm().toString());
        assertEquals(schematic, parameter.getSchematicSequent());
    }

    @Test(expected = RuleException.class)
    public void ambigiousTest() throws FormatException, TermBuildException, RuleException, DafnyParserException, DafnyException {
        TermParser tp = new TermParser(symbolTable);
        tp.setSchemaMode(true);
        Term schematic = tp.parse("_ < _");
        Sequent sequent = tp.parseSequent("i1 < i2 |- i1 < i2");
        TermParameter parameter = new TermParameter(schematic, sequent);
        parameter.getTermSelector();
    }

    @Test(expected = RuleException.class)
    public void notFoundTest() throws FormatException, TermBuildException, RuleException, DafnyParserException, DafnyException {
        TermParser tp = new TermParser(symbolTable);
        tp.setSchemaMode(true);
        Term schematic = tp.parse("_ > _");
        Sequent sequent = tp.parseSequent("i1 < i2 |- i1 < i2");
        TermParameter parameter = new TermParameter(schematic, sequent);
        parameter.getTermSelector();
    }

    @Test
    public void termSelectorAfterTerm() throws Exception {
        TermParser tp = new TermParser(symbolTable);
        tp.setSchemaMode(true);
        Sequent schematic = tp.parseSequent("|- (?m: _ < _)");
        Sequent sequent = tp.parseSequent("i1 < i2 |- i1 < i2");
        TermParameter parameter = new TermParameter(schematic, sequent);
        assertEquals(tp.parse("i1 < i2"), parameter.getTerm());
        assertEquals(new TermSelector(SequentPolarity.SUCCEDENT, 0), parameter.getTermSelector());
    }

    @Test
    public void termMatchAsSchemaVar() throws Exception {
        TermParser tp = new TermParser(symbolTable);
        tp.setSchemaMode(true);
        Sequent schematic = tp.parseSequent("|- ?m < _");
        Sequent sequent = tp.parseSequent("i1 < i2 |- i3 < i4");
        TermParameter parameter = new TermParameter(schematic, sequent);
        assertEquals(tp.parse("i3"), parameter.getTerm());
        assertEquals(new TermSelector(SequentPolarity.SUCCEDENT, 0, 0), parameter.getTermSelector());
    }

    @Test
    public void matchFunctionArgs() throws Exception {
        TermParser tp = new TermParser(symbolTable);
        tp.setSchemaMode(true);
        Term schematic = tp.parse("a(_)");
        Sequent sequent = tp.parseSequent("|- a(4) == 5");
        TermParameter parameter = new TermParameter(schematic, sequent);
        assertEquals(tp.parse("a(4)"), parameter.getTerm());
        assertEquals(new TermSelector(SequentPolarity.SUCCEDENT, 0, 0), parameter.getTermSelector());
    }


    @Test(expected = RuleException.class)
    public void noMatchButSchemaTerm() throws Exception {
        TermParser tp = new TermParser(symbolTable);
        tp.setSchemaMode(true);
        Term schematic = tp.parse("... ?x+1 ...");
        Sequent sequent = tp.parseSequent("i1+1 < i2 |- i1 < i2");
        TermParameter parameter = new TermParameter(schematic, sequent);
        assertEquals(new TermSelector(SequentPolarity.ANTECEDENT, 0), parameter.getTermSelector());
        assertEquals(tp.parse("i1 + 1 < i2"), parameter.getTerm());
    }

    @Test
    public void noMatchButSchemaTerm2() throws Exception {
        TermParser tp = new TermParser(symbolTable);
        tp.setSchemaMode(true);
        Term schematic = tp.parse("?x+1");
        Sequent sequent = tp.parseSequent("i1+1 < i2 |- i1 < i2");
        TermParameter parameter = new TermParameter(schematic, sequent);
        assertEquals(new TermSelector(SequentPolarity.ANTECEDENT, 0, 0), parameter.getTermSelector());
        assertEquals(tp.parse("i1 + 1"), parameter.getTerm());
    }

    @Test
    public void matchInSchemaTerm() throws Exception {
        TermParser tp = new TermParser(symbolTable);
        tp.setSchemaMode(true);
        Term schematic = tp.parse("(?m: ?x+1)");
        Sequent sequent = tp.parseSequent("i1+1 < i2 |- i1 < i2");
        TermParameter parameter = new TermParameter(schematic, sequent);
        assertEquals(new TermSelector(SequentPolarity.ANTECEDENT, 0, 0), parameter.getTermSelector());
        assertEquals(tp.parse("i1 + 1"), parameter.getTerm());
    }

    @Test
    public void noMatchInSequent() throws Exception {
        TermParser tp = new TermParser(symbolTable);
        tp.setSchemaMode(true);
        Sequent schematic = tp.parseSequent("|- _ < _");
        Sequent sequent = tp.parseSequent("i1 < i2 |- i3 < i4");
        TermParameter parameter = new TermParameter(schematic, sequent);
        assertEquals(tp.parse("i3 < i4"), parameter.getTerm());
        assertEquals(new TermSelector(SequentPolarity.SUCCEDENT, 0), parameter.getTermSelector());
    }

    @Test
    public void SchematicTermToSequentTest2() throws FormatException, TermBuildException, RuleException, DafnyParserException, DafnyException {
        TermParser tp = new TermParser(symbolTable);
        tp.setSchemaMode(true);
        Term schematic = tp.parse("_ < _");
        Sequent sequent = tp.parseSequent("i1 < i2 |- i1 + i2 > 0");
        TermParameter parameter = new TermParameter(schematic, sequent);
        assertEquals(new TermSelector("A.0"), parameter.getTermSelector());
        assertEquals("$lt(_, _) |-", parameter.getMatchParameter().toString());
        assertEquals(schematic, parameter.getSchematicTerm());
        assertEquals("$lt(i1, i2)", parameter.getTerm().toString());
    }

    @Test
    public void SchematicTermToSequentTest3() throws FormatException, TermBuildException, RuleException, DafnyParserException, DafnyException {
        TermParser tp = new TermParser(symbolTable);
        tp.setSchemaMode(true);
        Term schematic = tp.parse("_ < (?m: _)");
        Sequent sequent = tp.parseSequent("i1 < i2 |- i1 + i2 > 0");
        TermParameter parameter = new TermParameter(schematic, sequent);
        assertEquals(new TermSelector("A.0.1"), parameter.getTermSelector());
        assertEquals("$lt(_, (?m: _)) |-", parameter.getMatchParameter().toString());
        assertEquals(schematic, parameter.getSchematicTerm());
        assertEquals("i2", parameter.getTerm().toString());
    }

    @Test
    public void toStringTest() throws FormatException, TermBuildException, RuleException, DafnyParserException, DafnyException {
        TermParser tp = new TermParser(symbolTable);
        tp.setSchemaMode(true);
        Term schematic = tp.parse("_ < (?m: _)");
        Sequent sequent = tp.parseSequent("i1 < i2 |- i1 + i2 > 0");
        TermParameter parameter = new TermParameter(schematic, sequent);
        assertEquals("TermParameter[originally a schematic term, " +
                        "term = null, schematicTerm = $lt(_, (?m: _)), schematicSequent = null, termSelector = null]",
                parameter.toString());
        parameter.getTermSelector();
        assertEquals("TermParameter[originally a schematic term, " +
                        "term = null, schematicTerm = $lt(_, (?m: _)), schematicSequent = null, termSelector = A.0.1]",
                parameter.toString());
    }
}
