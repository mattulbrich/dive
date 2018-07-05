/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 *
 */

package edu.kit.iti.algover.parser;

import edu.kit.iti.algover.util.TestUtil;
import org.junit.Test;

import static org.junit.Assert.*;

public class QuantifierGuardRemovalVisitorTest {

    @Test
    public void forallTest() throws Exception {
        DafnyTree exp = TestUtil.toTree(
                DafnyParser::expression,
                "forall i | i > 1 :: i > 0");

        new QuantifierGuardRemovalVisitor().walk(exp);

        assertEquals("(forall i (IMPLIES (> i 1) (> i 0)))", exp.toStringTree());
    }

    // from a bug
    @Test
    public void forallWithImplicitTypeTest() throws Exception {
        DafnyTree exp = TestUtil.toTree(
                DafnyParser::expression,
                "forall i | i > 1 :: i > 0");

        new QuantifierGuardRemovalVisitor().walk(exp);
        new ImplicitlyTypedVariableVisitor().walk(exp);

        assertEquals("(forall i (TYPE int) (IMPLIES (> i 1) (> i 0)))", exp.toStringTree());
    }

    @Test
    public void existsTest() throws Exception {
        DafnyTree exp = TestUtil.toTree(
                DafnyParser::expression,
                "exists i | i > 1 :: i > 0");

        new QuantifierGuardRemovalVisitor().walk(exp);

        assertEquals("(exists i (AND (> i 1) (> i 0)))", exp.toStringTree());
    }

}