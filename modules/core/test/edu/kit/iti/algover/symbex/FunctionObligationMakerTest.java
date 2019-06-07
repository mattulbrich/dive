/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.symbex;

import edu.kit.iti.algover.dafnystructures.DafnyFunction;
import edu.kit.iti.algover.parser.DafnyTree;
import edu.kit.iti.algover.parser.ParserTest;
import edu.kit.iti.algover.project.Project;
import edu.kit.iti.algover.util.TestUtil;
import org.junit.Test;
import org.junit.runners.Parameterized.Parameters;

import java.io.InputStream;
import java.util.List;

import static org.junit.Assert.*;

public class FunctionObligationMakerTest {

    @Test
    public void testFib() throws Exception {
        InputStream stream = getClass().getResourceAsStream("fib.dfy");
        DafnyTree parseTree = ParserTest.parseFile(stream);
        Project p = TestUtil.mockProject(parseTree);

        DafnyFunction fib = p.getFunction("fib");
        FunctionObligationMaker fom = new FunctionObligationMaker();

        List<SymbexPath> paths = fom.visit(fib.getRepresentation());
        int i = 0;
        {
            SymbexPath path = paths.get(i++);
            assertEquals("[PRE[null]:(>= n 0)]",
                    path.getPathConditions().toString());
            assertEquals("[CALL_PRE[fib]:(==> (not (== n 0)) (==> (not (== n 1)) (LET (VAR n) (- n 1) (>= n 0))))]",
                    path.getProofObligations().toString());
            assertEquals(0, path.getAssignmentHistory().size());
        }
        {
            SymbexPath path = paths.get(i++);
            assertEquals("[PRE[null]:(>= n 0)]",
                    path.getPathConditions().toString());
            assertEquals("[VARIANT_DECREASED[fib]:(==> (not (== n 0)) (==> (not (== n 1)) " +
                            "(NOETHER_LESS (LISTEX (LET (VAR n) (- n 1) n)) (LISTEX n))))]",
                    path.getProofObligations().toString());
            assertEquals(0, path.getAssignmentHistory().size());
        }
        {
            SymbexPath path = paths.get(i++);
            assertEquals("[PRE[null]:(>= n 0)]",
                    path.getPathConditions().toString());
            assertEquals("[CALL_PRE[fib]:(==> (not (== n 0)) (==> (not (== n 1)) (LET (VAR n) (- n 2) (>= n 0))))]",
                    path.getProofObligations().toString());
            assertEquals(0, path.getAssignmentHistory().size());
        }
        {
            SymbexPath path = paths.get(i++);
            assertEquals("[PRE[null]:(>= n 0)]",
                    path.getPathConditions().toString());
            assertEquals("[VARIANT_DECREASED[fib]:(==> (not (== n 0)) (==> (not (== n 1)) " +
                            "(NOETHER_LESS (LISTEX (LET (VAR n) (- n 2) n)) (LISTEX n))))]",
                    path.getProofObligations().toString());
            assertEquals(0, path.getAssignmentHistory().size());
        }
        assertEquals(i, paths.size());
    }

}