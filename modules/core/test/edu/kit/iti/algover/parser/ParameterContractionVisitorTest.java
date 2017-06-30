/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.parser;

import org.junit.Test;

import edu.kit.iti.algover.util.TreeUtil;

import static org.junit.Assert.*;

public class ParameterContractionVisitorTest {

    // helped find a bug
    @Test
    public void test() throws Exception {

        DafnyTree tree = ParserTest.parseFile(
                getClass().getResourceAsStream("typeParameters.dfy"));

        DafnyTree op = TreeUtil.traverse(tree, 0, 2, 0);

        assertEquals("(CALL ($internal Param1 (Param2 Param3 Param4)) (ARGS ($internal2 X) 0))", op.toStringTree());
        assertEquals(DafnyParser.LOGIC_ID, op.getChild(0).getType());

        op.accept(new ParameterContractionVisitor(), null);

        assertEquals("(CALL $internal<Param1,Param2<Param3,Param4>> (ARGS $internal2<X> 0))", op.toStringTree());
        assertEquals(DafnyParser.ID, op.getChild(0).getType());
    }

}
