/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 *
 */

package edu.kit.iti.algover.parser;

import edu.kit.iti.algover.project.Project;
import edu.kit.iti.algover.util.ASTUtil;
import edu.kit.iti.algover.util.TestUtil;
import junitparams.JUnitParamsRunner;
import junitparams.Parameters;
import org.junit.Test;
import org.junit.runner.RunWith;

import static org.junit.Assert.*;


@RunWith(JUnitParamsRunner.class)
public class ModifiesListResolverTest {

    public static Object[][] parametersForTestModifies() {
        return new String[][] {
                {
                        "method m(o: object) modifies {o} {}",
                        "({ o)"
                },
                {
                        "method m(o: object, p: object) modifies {o, p} {}",
                        "({ o p)"
                },
                {
                        "method m(o: object) modifies o {}",
                        "(SETEX o)"
                },
                {
                        "method m(a: array<int>) modifies a {}",
                        "(SETEX a)"
                },
                {
                        "method m(o: object, p: object) modifies o, p {}",
                        "(SETEX o p)"
                },
                {
                        "method m(so: set<object>) modifies so {}",
                        "so"
                },
                {
                        "method m(s1: set<object>, s2: set<object>, s3: set<object>) modifies s1, s2, s3 {}",
                        "(PLUS (PLUS s1 s2) s3)"
                },
                {
                        "method m(s1: set<object>, s2: set<object>, s3: set<object>) modifies s1, s2, s3 {}",
                        "(PLUS (PLUS s1 s2) s3)"
                },
        };
    }

    @Test @Parameters
    public void testModifies(String code, String expected) throws Exception {

        Project p = TestUtil.mockProject(code);

        DafnyTree modifies = p.getMethod("m").getModifiesClause();

//        System.out.println(modifies.toStringTree());
        DafnyTree actual = ModifiesListResolver.resolve(modifies);
//        System.out.println(modifies.toStringTree());

        assertEquals(expected, actual.toStringTree());
        assertEquals("(set object)", actual.getExpressionType().toStringTree());

    }

    @Test
    public void testEmpty() throws Exception {

        Project p = TestUtil.mockProject("method m() {}");

        DafnyTree modifies = ASTUtil.create(DafnyParser.MODIFIES);

        DafnyTree actual = ModifiesListResolver.resolve(modifies);

        assertEquals("SETEX", actual.toStringTree());
        assertEquals("(set object)", actual.getExpressionType().toStringTree());

    }


}