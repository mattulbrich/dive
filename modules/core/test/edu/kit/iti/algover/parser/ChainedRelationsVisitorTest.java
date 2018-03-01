/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 *
 */

package edu.kit.iti.algover.parser;

import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.ExpectedException;

import java.io.ByteArrayInputStream;
import java.io.IOException;

import static org.junit.Assert.*;

public class ChainedRelationsVisitorTest {
    @Rule
    public ExpectedException thrown = ExpectedException.none();

    @Test
    public void testLess() throws IOException, DafnyParserException, DafnyException {
        String s = "method m() ensures 1 < 2 < 3 {}";
        DafnyTree t = ParserTest.parseFile(new ByteArrayInputStream(s.getBytes()));

        new ChainedRelationsVisitor().walk(t);

        assertEquals("(COMPILATION_UNIT " +
                "(method m ARGS (ensures " +
                "(&& (< 1 2) (< 2 3))) BLOCK))", t.toStringTree());
    }

    @Test
    public void testGreater() throws IOException, DafnyParserException, DafnyException {
        String s = "method m() ensures 3 >= 3 > 2 {}";
        DafnyTree t = ParserTest.parseFile(new ByteArrayInputStream(s.getBytes()));

        new ChainedRelationsVisitor().walk(t);

        assertEquals("(COMPILATION_UNIT " +
                "(method m ARGS (ensures " +
                "(&& (>= 3 3) (> 3 2))) BLOCK))", t.toStringTree());
    }

    @Test
    public void testMixed() throws IOException, DafnyParserException, DafnyException {
        String s = "method m() ensures 2 < 3 > 2 {}";
        DafnyTree t = ParserTest.parseFile(new ByteArrayInputStream(s.getBytes()));

        thrown.expect(DafnyException.class);
        thrown.expectMessage("Illegally chained relational expression");
        new ChainedRelationsVisitor().walk(t);
    }


}