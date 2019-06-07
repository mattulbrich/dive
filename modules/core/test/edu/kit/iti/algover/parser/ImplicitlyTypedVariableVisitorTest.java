/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.parser;

import edu.kit.iti.algover.util.TestUtil;
import org.junit.Test;

import static org.junit.Assert.*;

public class ImplicitlyTypedVariableVisitorTest {

    @Test
    public void quantifierTest() throws Exception {
        DafnyTree exp = TestUtil.toTree(
                DafnyParser::expression,
                "forall i :: i > 0");

        new ImplicitlyTypedVariableVisitor().walk(exp);

        assertEquals("(forall i (TYPE int) (> i 0))", exp.toStringTree());
        assertEquals(DafnyParser.INT, exp.getChild(1).getChild(0).getType());

    }

    @Test
    public void quantifierDoubleTest() throws Exception {

        DafnyTree exp = TestUtil.toTree(
                DafnyParser::expression,
                "forall i,j :: i > j");

        new ImplicitlyTypedVariableVisitor().walk(exp);

        assertEquals("(forall i j (TYPE int) (> i j))", exp.toStringTree());
        assertEquals(DafnyParser.INT, exp.getChild(2).getChild(0).getType());

    }

    @Test
    public void notypeadd() throws Exception {

        DafnyTree exp = TestUtil.toTree(
                DafnyParser::expression,
                "forall i : seq<int> :: i[0] > 0");

        new ImplicitlyTypedVariableVisitor().walk(exp);

        assertEquals("(forall i (TYPE (seq int)) (> (ARRAY_ACCESS i 0) 0))", exp.toStringTree());
        assertEquals(DafnyParser.SEQ, exp.getChild(1).getChild(0).getType());

    }

}