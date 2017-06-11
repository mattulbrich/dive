/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.term.builder;

import org.junit.Test;
import org.junit.runner.RunWith;

import static org.junit.Assert.*;

import edu.kit.iti.algover.data.BuiltinSymbols;
import edu.kit.iti.algover.parser.DafnyParserException;
import edu.kit.iti.algover.term.ApplTerm;
import edu.kit.iti.algover.term.FunctionSymbol;
import edu.kit.iti.algover.term.SchemaVarTerm;
import edu.kit.iti.algover.term.Sort;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.term.VariableTerm;
import edu.kit.iti.algover.term.parser.TermParser;
import junitparams.JUnitParamsRunner;
import junitparams.Parameters;

@RunWith(JUnitParamsRunner.class)
public class ReplacementVisitorTest {

    private class CloneVisitor extends ReplacementVisitor<Void> {

        @Override
        public VariableTerm visitBoundVariable(VariableTerm variableTerm, Void arg) {
            if(variableTerm.getName().startsWith("_")) {
                return variableTerm;
            } else {
                return null;
            }
        }

        @Override
        public Term visit(VariableTerm variableTerm, Void arg) {
            return visitBoundVariable(variableTerm, arg);
        }

        @Override
        public Term visit(SchemaVarTerm schemaVarTerm, Void arg) {
            if(schemaVarTerm.getName().startsWith("_")) {
                return schemaVarTerm;
            } else {
                return null;
            }
        }

        @Override
        public Term visit(ApplTerm applTerm, Void arg) throws TermBuildException {
            if(applTerm.countTerms() == 0
                    && applTerm.getFunctionSymbol().getName().startsWith("_")) {
                return applTerm;
            } else {
                return super.visit(applTerm, arg);
            }
        }

        @Override
        public VariableTerm visitLetTarget(VariableTerm x, Void arg) throws TermBuildException {
            return visitBoundVariable(x, null);
        }
    }

    public String[][] parametersForTestIdentity() {
        return new String[][] {
            { "_i" }, { "i + _i" }, { "_i + i" }, { "_i + _i" },
            { "forall _x: int :: i > _x" },
            { "forall _x: int :: _i > _x" },
            { "forall x: int :: _i > x" },
            { "forall _x: int :: i+1 > i" },
            { "let x, _y, z, _a := 1, _i+1, _i-1, i+1; _y + 1" }, // revealed a bug
            { "let y := _i + 1; y + i" },
            { "let y := i + 1; y + _i" },
        };
    }

    public String[] parametersForTestNull() {
        return new String[] {
            "i", "i + i",
            "forall x: int :: i > x",
            "let y := i + 1; y + i",
        };
    }

    // revealed a bug
    @Test @Parameters
    public void testIdentity(String test) throws DafnyParserException, TermBuildException {

        BuiltinSymbols s = new BuiltinSymbols();
        s.addFunctionSymbol(new FunctionSymbol("i", Sort.INT));
        s.addFunctionSymbol(new FunctionSymbol("_i", Sort.INT));
        CloneVisitor cloneVisitor = new CloneVisitor();

        Term term = TermParser.parse(s, test);
        Term actual = term.accept(cloneVisitor, null);
        assertNotNull(test, actual);
        assertEquals(test, term, actual);
    }

    // revealed a bug!
    @Test @Parameters
    public void testNull(String test) throws DafnyParserException, TermBuildException {
        BuiltinSymbols s = new BuiltinSymbols();
        s.addFunctionSymbol(new FunctionSymbol("i", Sort.INT));
        s.addFunctionSymbol(new FunctionSymbol("_i", Sort.INT));
        CloneVisitor cloneVisitor = new CloneVisitor();

        Term t = TermParser.parse(s, test);
        Term actual = t.accept(cloneVisitor, null);
        assertNull(actual);
    }
}
