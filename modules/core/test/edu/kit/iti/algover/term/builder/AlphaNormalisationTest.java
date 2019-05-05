/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 *
 */

package edu.kit.iti.algover.term.builder;

import edu.kit.iti.algover.data.BuiltinSymbols;
import edu.kit.iti.algover.term.FunctionSymbol;
import edu.kit.iti.algover.term.LetTerm;
import edu.kit.iti.algover.term.QuantTerm;
import edu.kit.iti.algover.term.Sort;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.term.TermVisitor;
import edu.kit.iti.algover.term.VariableTerm;
import edu.kit.iti.algover.term.parser.TermParser;
import edu.kit.iti.algover.util.Pair;
import junitparams.JUnitParamsRunner;
import junitparams.Parameters;
import org.junit.Before;
import org.junit.Ignore;
import org.junit.Test;
import org.junit.runner.RunWith;

import java.util.ArrayList;
import java.util.List;

import static org.junit.Assert.*;

@RunWith(JUnitParamsRunner.class)
public class AlphaNormalisationTest {


    /**
     * This one removes "X" from variables. Used to create problems in inputs.
     */
    private static final TermVisitor<Void, Term, TermBuildException> UNDERSCORE_REMOVER =
            new ReplacementVisitor<Void>() {
                @Override
                public Term visit(VariableTerm v, Void arg) throws TermBuildException {
                    return visitBoundVariable(v, arg);
                }

                @Override
                public VariableTerm visitLetTarget(VariableTerm x, Void arg) throws TermBuildException {
                    return visitBoundVariable(x, arg);
                }

                @Override
                public VariableTerm visitBoundVariable(VariableTerm v, Void arg) throws TermBuildException {
                    if (v.getName().startsWith("X")) {
                        return new VariableTerm(v.getName().replaceAll("X", ""), v.getSort());
                    } else {
                        return null;
                    }
                }
            };

    private BuiltinSymbols table;

    public String[][] parametersForTestNormalise() {
        return new String[][] {
                { "let Xx := 3 :: Xx + x" , "let x_1 := 3 :: x_1 + x" },
                { "let Xx := 3 :: let Xx := 5 :: Xx + x" , "let x_1 := 3 :: let x_1 := 5 :: x_1 + x" },
                { "(let Xx := 3 :: Xx + x) + (let Xx := 3 :: Xx)" , "(let x_1 := 3 :: x_1 + x) + (let x := 3 :: x)" },
                { "forall Xx :: Xx > x", "forall x_1 :: x_1 > x" },
                { "forall Xy:int :: forall y:bool :: (y == true && Xy == 5)",
                  "forall y:int :: forall y_1:bool :: (y_1 == true && y == 5)" },
                { "let Xx := 3 :: let Xx := Xx+1 :: Xx==x",
                  "let x_1 := 3 :: let x_1 := x_1+1 :: x_1==x" },
                { "let Xy := 3 :: let y := true :: y && Xy > 0",
                  "let y := 3 :: let y_1 := true :: y_1 && y > 0" },
                { "let XXXx := [1] :: let XXx := true :: let Xx := 1 :: XXXx[Xx] == x && XXx",
                  "let x_1 := [1] :: let x_2 := true :: let x_3 := 1 :: x_1[x_3] == x && x_2" },
                { "let XXXx := 1 :: let XXx := [1] :: let Xx := 2 :: XXx[0] == Xx + XXXx",
                  "let x := 1 :: let x := [1] :: let x_1 := 2 :: x[0] == x_1 + x_1" },
        };
    }

    public Object[][] parametersForTestIsNormalised() {
        return new Object[][] {
                { "let x := x + 3 :: let x := x + 1 :: x + 2", true },
                { "let Xx := 3 :: Xx + x" , false },
                { "let x := true :: let x:= 5 :: x > 0" , true },
                { "let Xx := true :: let x:= 5 :: Xx && x > 0" , false },
                { "forall Xx :: Xx == x", false },
                { "(forall Xx :: Xx == 5) && x==1", true },
                { "let XXXx := [1] :: let XXx := true :: let Xx := 1 :: XXXx[Xx] == x && XXx", false },
                };
    }

    @Before
    public void setup() {
        this.table = new BuiltinSymbols();
        table.addFunctionSymbol(new FunctionSymbol("x", Sort.INT));
        table.addFunctionSymbol(new FunctionSymbol("f", Sort.INT, Sort.INT));
    }

    @Test @Parameters
    public void testNormalise(String input, String expected) throws Exception {
        Term term = TermParser.parse(table, input);
        term = term.accept(UNDERSCORE_REMOVER, null);


        Term result = AlphaNormalisation.normalise(term);
        Term expectedTerm = TermParser.parse(table, expected);

        assertEquals("Alpha conversion for " + term.toString(), expectedTerm, result);
        assertTrue(AlphaNormalisation.isNormalised(result));
    }

    @Test @Parameters
    public void testIsNormalised(String input, Boolean expected) throws Exception {

        Term term = TermParser.parse(table, input);
        Term term2 = term.accept(UNDERSCORE_REMOVER, null);
        term = term2 == null ? term : term2;

        boolean result = AlphaNormalisation.isNormalised(term);

        assertEquals("isNormalised for " + term.toString(), expected, result);

    }
}