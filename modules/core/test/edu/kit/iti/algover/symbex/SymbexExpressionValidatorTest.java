/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 *
 */

package edu.kit.iti.algover.symbex;

import edu.kit.iti.algover.dafnystructures.DafnyFunction;
import edu.kit.iti.algover.dafnystructures.DafnyMethod;
import edu.kit.iti.algover.dafnystructures.TarjansAlgorithm;
import edu.kit.iti.algover.parser.DafnyException;
import edu.kit.iti.algover.parser.DafnyParser;
import edu.kit.iti.algover.parser.DafnyParserException;
import edu.kit.iti.algover.parser.DafnyTree;
import edu.kit.iti.algover.project.Project;
import edu.kit.iti.algover.util.ASTUtil;
import edu.kit.iti.algover.util.TestUtil;
import edu.kit.iti.algover.util.TreeUtil;
import junitparams.JUnitParamsRunner;
import junitparams.Parameters;
import org.antlr.runtime.RecognitionException;
import org.junit.Test;
import org.junit.runner.RunWith;

import java.io.IOException;
import java.util.Arrays;
import java.util.Deque;
import java.util.LinkedList;
import java.util.List;

import static org.junit.Assert.*;

@RunWith(JUnitParamsRunner.class)
public class SymbexExpressionValidatorTest {

    public Object[][] parametersForTestValid() {
        return new Object[][]{
                {
                        "method m(a: array<int>) ensures a[0] == 0 {}",
                        new int[]{0, 2, 0},
                        Arrays.asList("[][RT_IN_BOUNDS:(>= 0 0), RT_IN_BOUNDS:(< 0 (Length a))]",
                                "[][RT_NONNULL:(!= a null)]")
                },
                {
                        "method m(a: array2<int>) ensures a[0,22] == 0 {}",
                        new int[]{0, 2, 0},
                        Arrays.asList(
                                "[][RT_IN_BOUNDS:(>= 22 0), RT_IN_BOUNDS:(< 22 (Length1 a))]",
                                "[][RT_IN_BOUNDS:(>= 0 0), RT_IN_BOUNDS:(< 0 (Length0 a))]",
                                "[][RT_NONNULL:(!= a null)]")
                },
                {
                        "method m(a: seq<int>) ensures a[0] == 0 {}",
                        new int[]{0, 2, 0},
                        Arrays.asList("[][RT_IN_BOUNDS:(>= 0 0), RT_IN_BOUNDS:(< 0 (Length a))]")
                },
                {
                        "method m(x: int) ensures 1/x == 1 {}",
                        new int[]{0, 2, 0},
                        Arrays.asList("[][RT_IN_BOUNDS:(!= x 0)]")
                },
                {
                        "method m(x: int) ensures 1/x == 1/x {}",
                        new int[]{0, 2, 0},
                        Arrays.asList("[][RT_IN_BOUNDS:(!= x 0)]", "[][RT_IN_BOUNDS:(!= x 0)]")
                },
                {
                        "class C { var f:int; } method m(c: C) ensures c.f == 1 {}",
                        new int[]{1, 2, 0},
                        Arrays.asList("[][RT_NONNULL:(!= c null)]")
                },
                {
                        "class C { var f:int; method m() ensures this.f == 1 {} }",
                        new int[]{0, 2, 2, 0},
                        Arrays.asList()
                },
                {
                        "class C { var next:C; method m() ensures next.next == next {} }",
                        new int[]{0, 2, 2, 0},
                        Arrays.asList("[][RT_NONNULL:(!= next null)]")
                },

                // Logical shortcut operators
                {
                        "method m(a: int) ensures (a!=0 && 1/a > 0) && (1/a == 2) {}",
                        new int[]{0, 2, 0},
                        Arrays.asList(
                                "[GUARD_IN_EXPRESSION[null]:(&& (!= a 0) (> (/ 1 a) 0))][RT_IN_BOUNDS:(!= a 0)]",
                                "[GUARD_IN_EXPRESSION[null]:(!= a 0)][RT_IN_BOUNDS:(!= a 0)]")
                },
                {
                        "method m(a: int) ensures a!=0 && (1/a > 0 && 1/a == 2) {}",
                        new int[]{0, 2, 0},
                        Arrays.asList(
                                "[GUARD_IN_EXPRESSION[null]:(!= a 0), " +
                                        "GUARD_IN_EXPRESSION[null]:(> (/ 1 a) 0)][RT_IN_BOUNDS:(!= a 0)]",
                                "[GUARD_IN_EXPRESSION[null]:(!= a 0)][RT_IN_BOUNDS:(!= a 0)]")
                },
                {
                        "method m(a: int) ensures a!=0 ==> a > 0 ==> 1/a >= 2 {}",
                        new int[]{0, 2, 0},
                        Arrays.asList("[GUARD_IN_EXPRESSION[null]:(!= a 0), " +
                                "GUARD_IN_EXPRESSION[null]:(> a 0)][RT_IN_BOUNDS:(!= a 0)]")
                },
                {
                        // Left hand sides!
                        "method m(a: int) ensures 1/a==0 || (1/a==1 && (1/a==2 ==> true)) {}",
                        new int[]{0, 2, 0},
                        Arrays.asList(
                                "[GUARD_IN_EXPRESSION[null]:(not (== (/ 1 a) 0)), " +
                                        "GUARD_IN_EXPRESSION[null]:(== (/ 1 a) 1)][RT_IN_BOUNDS:(!= a 0)]",
                                "[GUARD_IN_EXPRESSION[null]:(not (== (/ 1 a) 0))][RT_IN_BOUNDS:(!= a 0)]",
                                "[][RT_IN_BOUNDS:(!= a 0)]")
                },
                {
                        "method m(a: int) ensures if 1/a==a then a/2==1 else a/3==1 {}",
                        new int[]{0, 2, 0},
                        Arrays.asList(
                                "[GUARD_IN_EXPRESSION[null]:(not (== (/ 1 a) a))][RT_IN_BOUNDS:(!= 3 0)]",
                                "[GUARD_IN_EXPRESSION[null]:(== (/ 1 a) a)][RT_IN_BOUNDS:(!= 2 0)]",
                                "[][RT_IN_BOUNDS:(!= a 0)]")
                },
                {
                        "method m(a: int) ensures a==0 || 1/a >= 2 {}",
                        new int[]{0, 2, 0},
                        Arrays.asList("[GUARD_IN_EXPRESSION[null]:(not (== a 0))][RT_IN_BOUNDS:(!= a 0)]")
                },

                // Function invocations
                {
                        "method m() ensures f(22)==2 {}\n" +
                                "function f(x: int) : int requires x >= 0 decreases x\n" +
                                "{ if x == 0 then 0 else f(x-1)+1 } ",
                        new int[]{0, 2, 0},
                        Arrays.asList("[][CALL_PRE[f]:(LET (VAR x) 22 (>= x 0))]")
                },
                {
                        // with decreases.
                        "function base(x: int) : int requires x >= 0 decreases x\n" +
                                "{ if x == 0 then 0 else base(x-1)+1 } ",
                        new int[]{0},
                        Arrays.asList("[GUARD_IN_EXPRESSION[null]:(not (== x 0))][CALL_PRE[base]:(LET (VAR x) (- x 1) (>= x 0))]",
                                "[GUARD_IN_EXPRESSION[null]:(not (== x 0))]" +
                                        "[VARIANT_DECREASED[base]:" +
                                        "(LET (VAR x) (- x 1) (NOETHER_LESS (LISTEX (LET (VAR x) (- x 1) x)) (LISTEX $decr)))]")
                },
                {
                    "class C { var next:C;\n" +
                            "   function f(x:int) : int requires x>0 {x}\n" +
                            "   method m() ensures f(1) + this.f(2) + next.f(3) > 0 {} }",
                    new int[]{0, 3, 2},
                    Arrays.asList(
                            "[][CALL_PRE[f]:(LET (VAR x) 1 (> x 0))]",
                            "[][CALL_PRE[f]:(LET (VAR this x) this 2 (> x 0))]",
                            "[][CALL_PRE[f]:(LET (VAR this x) next 3 (> x 0))]",
                            "[][RT_NONNULL:(!= next null)]")
                },
                };
    }

    @Test @Parameters
    public void testValid(String code, int[] selectors, List<String> expected) throws DafnyParserException, RecognitionException, IOException, DafnyException {

        Project project = TestUtil.mockProject(code);
        DafnyTree root = project.getDafnyFiles().get(0).getRepresentation();
        DafnyTree expression = TreeUtil.traverse(root, selectors);

        if(TestUtil.VERBOSE) {
            System.out.println(expression.toStringTree());
        }

        SymbexExpressionValidator expVal = new SymbexExpressionValidator();
        Deque<SymbexPath> stack = new LinkedList<>();
        DafnyFunction baseFunction = project.getFunction("base");
        DafnyTree caller;
        if (baseFunction != null) {
            caller = baseFunction.getRepresentation();
        }  else {
            caller = ASTUtil.builtInVar("FAKE!");
            caller.setExpressionType(ASTUtil.create(TarjansAlgorithm.CALLGRAPH_SCC, "something"));
        }
        SymbexPath path = new SymbexPath(caller);
        expVal.handleExpression(stack, path, expression);

        assertEquals(expected.size(), stack.size());
        int i = 0;
        for (SymbexPath p : stack) {
            String actual = "" +
                    p.getPathConditions() +
                    p.getProofObligations();
            assertTrue(actual + " not expected", expected.contains(actual));
        }

    }

}