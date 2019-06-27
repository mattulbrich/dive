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
        symbolTable.addFunctionSymbol(new FunctionSymbol("$$a", Sort.INT, Sort.HEAP, Sort.INT));
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
        assertEquals(selector, p.getTermSelector());
    }

    @Test
    public void TermToTest() throws FormatException, TermBuildException, RuleException, DafnyParserException, DafnyException {
        TermParser tp = new TermParser(symbolTable);
        Term term = tp.parse("i1 < i2");
        Sequent sequent = tp.parseSequent("i1 < i2 |- i1 + i2 > 0");
        TermParameter parameter = new TermParameter(term, sequent);
        assertEquals(new TermSelector("A.0"), parameter.getTermSelector());
        assertEquals("(... (?match: $lt(i1, i2)) ...) |-", parameter.getSchematicSequent().toString());
        assertEquals(term, parameter.getTerm());
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
        Sequent schematic = tp.parseSequent("|- (?match: _ < _)");
        Sequent sequent = tp.parseSequent("i1 < i2 |- i1 < i2");
        TermParameter parameter = new TermParameter(schematic, sequent);
        assertEquals(tp.parse("i1 < i2"), parameter.getTerm());
        assertEquals(new TermSelector(SequentPolarity.SUCCEDENT, 0), parameter.getTermSelector());
    }

    @Test
    public void termMatchAsSchemaVar() throws Exception {
        TermParser tp = new TermParser(symbolTable);
        tp.setSchemaMode(true);
        Sequent schematic = tp.parseSequent("|- ?match < _)");
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
        Term schematic = tp.parse("(?match: ?x+1)");
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
        assertEquals("(... $lt(_, _) ...) |-", parameter.getSchematicSequent().toString());
        assertEquals(schematic, parameter.getSchematicTerm());
        assertEquals("$lt(i1, i2)", parameter.getTerm().toString());
    }

    @Test
    public void SchematicTermToSequentTest3() throws FormatException, TermBuildException, RuleException, DafnyParserException, DafnyException {
        TermParser tp = new TermParser(symbolTable);
        tp.setSchemaMode(true);
        Term schematic = tp.parse("_ < (?match: _)");
        Sequent sequent = tp.parseSequent("i1 < i2 |- i1 + i2 > 0");
        TermParameter parameter = new TermParameter(schematic, sequent);
        assertEquals(new TermSelector("A.0.1"), parameter.getTermSelector());
        assertEquals("(... $lt(_, (?match: _)) ...) |-", parameter.getSchematicSequent().toString());
        assertEquals(schematic, parameter.getSchematicTerm());
        assertEquals("i2", parameter.getTerm().toString());
    }

    @Test
    public void toStringTest() throws FormatException, TermBuildException, RuleException, DafnyParserException, DafnyException {
        TermParser tp = new TermParser(symbolTable);
        tp.setSchemaMode(true);
        Term schematic = tp.parse("_ < (?match: _)");
        Sequent sequent = tp.parseSequent("i1 < i2 |- i1 + i2 > 0");
        TermParameter parameter = new TermParameter(schematic, sequent);
        assertEquals("TermParameter[term = null, schematicTerm = $lt(_, (?match: _)), schematicSequent = null, TermSelector = null]",
                parameter.toString());
        parameter.getTermSelector();
        assertEquals("TermParameter[term = null, schematicTerm = $lt(_, (?match: _)), schematicSequent = null, TermSelector = A.0.1]",
                parameter.toString());
    }
}
