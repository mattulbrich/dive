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
import edu.kit.iti.algover.util.SymbexUtil;
import edu.kit.iti.algover.util.TestUtil;
import org.junit.Test;
import org.junit.runners.Parameterized.Parameters;

import java.io.InputStream;
import java.util.List;
import java.util.Properties;

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
            assertEquals("[PRE[null]:(>= n 0), PRE[null]:(== $mod SETEX)]",
                    path.getPathConditions().toString());
            assertEquals("[CALL_PRE[fib]:(==> (not (== n 0)) (==> (not (== n 1)) (LET (VAR n) (- n 1) (>= n 0))))]",
                    path.getProofObligations().toString());
            assertEquals(0, path.getAssignmentHistory().size());
        }
        {
            SymbexPath path = paths.get(i++);
            assertEquals("[PRE[null]:(>= n 0), PRE[null]:(== $mod SETEX)]",
                    path.getPathConditions().toString());
            assertEquals("[VARIANT_DECREASED[fib]:(==> (not (== n 0)) (==> (not (== n 1)) " +
                            "(NOETHER_LESS (LISTEX (LET (VAR n) (- n 1) n)) (LISTEX n))))]",
                    path.getProofObligations().toString());
            assertEquals(0, path.getAssignmentHistory().size());
        }
        {
            SymbexPath path = paths.get(i++);
            assertEquals("[PRE[null]:(>= n 0), PRE[null]:(== $mod SETEX)]",
                    path.getPathConditions().toString());
            assertEquals("[CALL_PRE[fib]:(==> (not (== n 0)) (==> (not (== n 1)) (LET (VAR n) (- n 2) (>= n 0))))]",
                    path.getProofObligations().toString());
            assertEquals(0, path.getAssignmentHistory().size());
        }
        {
            SymbexPath path = paths.get(i++);
            assertEquals("[PRE[null]:(>= n 0), PRE[null]:(== $mod SETEX)]",
                    path.getPathConditions().toString());
            assertEquals("[VARIANT_DECREASED[fib]:(==> (not (== n 0)) (==> (not (== n 1)) " +
                            "(NOETHER_LESS (LISTEX (LET (VAR n) (- n 2) n)) (LISTEX n))))]",
                    path.getProofObligations().toString());
            assertEquals(0, path.getAssignmentHistory().size());
        }
        assertEquals(i, paths.size());
    }

    /*
    class Node
{
  var next : Node?;
  var value : int;
  ghost var depth : int;
  ghost var footprint : set<object>;

  function Valid() : bool
    reads this, footprint
    decreases depth
  {
 1.   this in footprint &&
 2.     this.depth >= 0 &&
 3.     (this.next != null ==>
 4.       next in footprint &&
 5.       next.footprint <= footprint &&
 6.       0 <= next.depth < depth &&
 7.       next.Valid())
  }
}

0 - reads this in 1
1 - reads this in 2
2 - reads this in 3
3 - reads this in 4
4 - reads this in 4 (same)
5 - nonnull next.footprint in 5
6 - reads next in 5 next.footprint
7 - reads this in 5 this.next
8 - reads this in 5 this.footprint
9 - reads next in 6 next.depth
10 - reads this in 6 this.next
11 - reads this in 6 this.depth
12 - nonnull next.depth in 6
13 - reads this in 7 this.next
14 - nonnull next.Valid() in 7
15 - reads for recursive call
16 - termination next.Valid()

This is outdated ... but you get the idea ...

     */

    @Test
    public void testRecursiveValid() throws Exception {
        InputStream stream = getClass().getResourceAsStream("functions.dfy");
        DafnyTree parseTree = ParserTest.parseFile(stream);
        Project p = TestUtil.mockProject(parseTree);

        DafnyFunction valid = p.getClass("Node").getFunction("Valid");
        FunctionObligationMaker fom = new FunctionObligationMaker();

        List<SymbexPath> paths = fom.visit(valid.getRepresentation());

        for (SymbexPath path : paths) {
            assertEquals("[PRE[null]:(== $mod (PLUS (SETEX this) footprint))]", path.getPathConditions().toString());
        }

        Properties expected = new Properties();

        /*
        // To produce the oracle
        for (int i = 0; i < paths.size(); i++) {
            expected.put(Integer.toString(i),
                    paths.get(i).getProofObligations().toString());
        }
        expected.storeToXML(System.out, "Test oracle for FunctionObligationMakerTest");
        expected.clear();
        */

        try(InputStream propStream = getClass().getResourceAsStream("functions.dfy.xml")) {
            expected.loadFromXML(propStream);
        }
        assertEquals("Number of paths", expected.size(), paths.size());

        for (int i = 0; i < paths.size(); i++) {
            assertEquals(expected.get(Integer.toString(i)),
                    paths.get(i).getProofObligations().toString());
        }

    }
}