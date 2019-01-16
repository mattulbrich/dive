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
                public Term visit(LetTerm letTerm, Void arg) throws TermBuildException {
                    List<Pair<VariableTerm, Term>> subs = letTerm.getSubstitutions();
                    List<Pair<VariableTerm, Term>> newSubs = null;
                    int cnt = 0;
                    for (Pair<VariableTerm, Term> sub : subs) {
                        VariableTerm var = sub.fst;
                        if (var.getName().startsWith("X")) {
                            var = new VariableTerm(var.getName().substring(1), var.getSort());
                        } else {
                            var = null;
                        }
                        Term val = sub.snd.accept(this, null);
                        if(var != null || val != null || newSubs != null) {
                            if (var == null) {
                                var = sub.fst;
                            }
                            if (val == null) {
                                val = sub.snd;
                            }
                            if (newSubs == null) {
                                newSubs = new ArrayList<>(subs);
                            }
                            newSubs.set(cnt, new Pair<>(var, val));
                        }
                        cnt ++;
                    }

                    Term inner = letTerm.getTerm(0).accept(this, null);
                    if (inner != null || newSubs != null) {
                        if (inner == null ) {
                            inner = letTerm.getTerm(0);
                        }
                        if (newSubs == null) {
                            newSubs = subs;
                        }
                        return new LetTerm(newSubs, inner);
                    }

                    return null;
                }

                @Override
                public Term visit(VariableTerm v, Void arg) throws TermBuildException {
                    if (v.getName().startsWith("X")) {
                        return new VariableTerm(v.getName().substring(1), v.getSort());
                    } else {
                        return null;
                    }
                }

                @Override
                public Term visit(QuantTerm q, Void arg) throws TermBuildException {
                    VariableTerm var = q.getBoundVar();
                    VariableTerm newvar = (VariableTerm) var.accept(this, null);
                    Term matrix = q.getTerm(0).accept(this, null);
                    if (newvar != null || matrix != null) {
                        if(newvar == null) {
                            newvar = var;
                        }
                        if (matrix == null) {
                            matrix = q.getTerm(0);
                        }
                        return new QuantTerm(q.getQuantifier(), newvar, matrix);
                    }
                    return null;
                }
            };

    private BuiltinSymbols table;

    public String[][] parametersForTestNormalise() {
        return new String[][] {
                { "let Xx := 3 :: Xx + x" , "let x_1 := 3 :: x_1 + x" },
                { "let Xx := 3 :: let Xx := 5 :: Xx + x" , "let x_1 := let x_1 := 3 :: x_1 + x" },
                { "(let Xx := 3 :: Xx + x) + (let Xx := 3 :: Xx)" , "(let x_1 := 3 :: x_1 + x) + (let x := 3 :: x)" },
        };
    }

    public Object[][] parametersForTestIsNormalised() {
        return new Object[][] {
                { "let x := x + 3 :: let x := x + 1 :: x + 2", true },
                { "let Xx := 3 :: Xx + x" , false },
                { "let x := true :: let x:= 5 :: x > 0" , true },
                { "let Xx := true :: let x:= 5 :: Xx && x > 0" , false },
                };
    }

    @Before
    public void setup() {
        this.table = new BuiltinSymbols();
        table.addFunctionSymbol(new FunctionSymbol("x", Sort.INT));
        table.addFunctionSymbol(new FunctionSymbol("f", Sort.INT, Sort.INT));
    }

    @Test @Parameters @Ignore
    public void testNormalise(String input, String expected) throws Exception {
        Term term = TermParser.parse(table, input);
        term = term.accept(UNDERSCORE_REMOVER, null);

        Term result = AlphaNormalisation.normalise(term);
        Term expectedTerm = TermParser.parse(table, expected);

        assertEquals("Alpha conversion for " + term.toString(), expectedTerm, result);
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