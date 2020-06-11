/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.parser;

import edu.kit.iti.algover.KnownRegression;
import org.junit.Ignore;
import org.junit.Rule;
import org.junit.Test;
import org.junit.experimental.categories.Category;
import org.junit.rules.ExpectedException;

import java.io.ByteArrayInputStream;
import java.io.IOException;
import java.util.List;

import static org.junit.Assert.*;

public class ChainedRelationsVisitorTest {
    @Rule
    public ExpectedException thrown = ExpectedException.none();

    @Test
    public void testLess() throws IOException, DafnyParserException, DafnyException {
        String s = "method m() ensures 1 < 2 < 3 {}";
        DafnyTree t = ParserTest.parseFile(new ByteArrayInputStream(s.getBytes()));

        SyntacticSugarVistor.visitDeep(t, new ChainedRelationsVisitor());

        assertEquals("(COMPILATION_UNIT " +
                "(method m ARGS (ensures " +
                "(&& (< 1 2) (< 2 3))) BLOCK))", t.toStringTree());
    }

    @Test
    public void testGreater() throws IOException, DafnyParserException, DafnyException {
        String s = "method m() ensures 3 >= 3 > 2 {}";
        DafnyTree t = ParserTest.parseFile(new ByteArrayInputStream(s.getBytes()));

        SyntacticSugarVistor.visitDeep(t, new ChainedRelationsVisitor());

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
        SyntacticSugarVistor.visitDeep(t, new ChainedRelationsVisitor());
    }

    @Test
    public void testSemiAscend() throws IOException, DafnyParserException, DafnyException {
        String s = "method m() ensures 6 >= 3 == 3 {}";
        DafnyTree t = ParserTest.parseFile(new ByteArrayInputStream(s.getBytes()));

        SyntacticSugarVistor.visitDeep(t, new ChainedRelationsVisitor());

        assertEquals("(COMPILATION_UNIT " +
                "(method m ARGS (ensures " +
                "(&& (>= 6 3) (== 3 3))) BLOCK))", t.toStringTree());
    }

    @Test
    public void testOneDirectionDesc() throws IOException, DafnyParserException, DafnyException {
        String s = "method m() ensures 6 >= 3 == 3 <= 5 {}";
        DafnyTree t = ParserTest.parseFile(new ByteArrayInputStream(s.getBytes()));

        thrown.expect(DafnyException.class);
        thrown.expectMessage("Illegally chained relational expression");
        SyntacticSugarVistor.visitDeep(t, new ChainedRelationsVisitor());
        System.out.println(t.toStringTree());
    }

    @Test
    public void testOneDirectionAsc() throws IOException, DafnyParserException, DafnyException {
        String s = "method m() ensures 1 < 3 > 2 {}";
        DafnyTree t = ParserTest.parseFile(new ByteArrayInputStream(s.getBytes()));

        thrown.expect(DafnyException.class);
        thrown.expectMessage("Illegally chained relational expression");
        SyntacticSugarVistor.visitDeep(t, new ChainedRelationsVisitor());
        System.out.println(t.toStringTree());
    }

    @Test
    @Category(KnownRegression.class)
    public void testNotTooEager() throws IOException, DafnyParserException, DafnyException {
        String s = "method m(x:int) ensures (x<5) == (x-5<0) {}";
        DafnyTree t = ParserTest.parseFile(new ByteArrayInputStream(s.getBytes()));

        String expected = t.toStringTree();
        SyntacticSugarVistor.visitDeep(t, new ChainedRelationsVisitor());
        assertEquals(expected, t.toStringTree());
    }

    @Test
    public void testEq() throws IOException, DafnyParserException, DafnyException {
        String s = "method m() ensures 6 == 3 == 3 {}";
        DafnyTree t = ParserTest.parseFile(new ByteArrayInputStream(s.getBytes()));

        SyntacticSugarVistor.visitDeep(t, new ChainedRelationsVisitor());

        assertEquals("(COMPILATION_UNIT " +
                "(method m ARGS (ensures " +
                "(&& (== 6 3) (== 3 3))) BLOCK))", t.toStringTree());
    }

    @Test
    public void testParens() throws Exception {
        String s = "method m() ensures true == (3 == 3) {}";
        DafnyTree t = ParserTest.parseFile(new ByteArrayInputStream(s.getBytes()));

        SyntacticSugarVistor.visitDeep(t, new ChainedRelationsVisitor());

        assertEquals("(COMPILATION_UNIT " +
                "(method m ARGS (ensures " +
                "(== true (== 3 3))) BLOCK))", t.toStringTree());
    }

    @Test
    public void fixBug176() throws Exception {
        DafnyTree full = ParserTest.parseFile(getClass().getResourceAsStream("chainedRelations.dfy"));
        List<DafnyTree> requires = full.getChild(0).getChildrenWithType(DafnyParser.REQUIRES);
        {
            SyntacticSugarVistor.visitDeep(requires.get(0), new ChainedRelationsVisitor());
            assertEquals("(requires (&& (== x y) (== y z)))",
                    requires.get(0).toStringTree());
        }
        {
            SyntacticSugarVistor.visitDeep(requires.get(1), new ChainedRelationsVisitor());
            assertEquals("(requires (&& (> x y) (>= y z)))",
                    requires.get(1).toStringTree());
        }
        {
            SyntacticSugarVistor.visitDeep(requires.get(2), new ChainedRelationsVisitor());
            assertEquals("(requires (&& (> x y) (== y z)))",
                    requires.get(2).toStringTree());
        }
        {
            System.out.println(full.toStringTree());
            SyntacticSugarVistor.visitDeep(requires.get(3), new ChainedRelationsVisitor());
            assertEquals("(requires (&& (== x y) (>= y z)))",
                    requires.get(3).toStringTree());
        }
        {
            SyntacticSugarVistor.visitDeep(requires.get(4), new ChainedRelationsVisitor());
            assertEquals("(requires (== (> x 0) true))",
                    requires.get(4).toStringTree());
        }
        {
            SyntacticSugarVistor.visitDeep(requires.get(5), new ChainedRelationsVisitor());
            assertEquals("(requires (== (== x 0) true))",
                    requires.get(5).toStringTree());
        }
        {
            SyntacticSugarVistor.visitDeep(requires.get(6), new ChainedRelationsVisitor());
            assertEquals("(requires (&& (< (+ x 1) (+ x 2)) (< (+ x 2) (+ x 3))))",
                    requires.get(6).toStringTree());
        }

    }
}
