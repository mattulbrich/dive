/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 *
 */

package edu.kit.iti.algover.dafnystructures;

import edu.kit.iti.algover.parser.DafnyException;
import edu.kit.iti.algover.parser.DafnyParserException;
import edu.kit.iti.algover.parser.DafnyTree;
import edu.kit.iti.algover.parser.ParserTest;
import edu.kit.iti.algover.project.Project;
import edu.kit.iti.algover.util.TestUtil;
import org.antlr.runtime.RecognitionException;
import org.junit.Before;
import org.junit.Test;

import java.io.IOException;
import java.io.InputStream;
import java.util.Map;

import static org.junit.Assert.*;

public class TarjansAlgorithmTest {

    private Project project;

    @Before
    public void setup() throws Exception {
        InputStream stream = getClass().getResourceAsStream("tarjan.dfy");
        DafnyTree fileTree = ParserTest.parseFile(stream);

        // performs type analysis etc:
        this.project = TestUtil.mockProject(fileTree);
    }

    @Test
    public void testSCCComputation() throws Exception {
        TarjansAlgorithm ta = new TarjansAlgorithm(project);
        ta.computeSCCs();

        fail("implement test here");

        System.out.println();
    }

    @Test
    public void testComputeDecls() throws Exception {
        TarjansAlgorithm ta = new TarjansAlgorithm(project);

        Object x1Dep = TestUtil.call(ta, "getCalledDecls", project.getMethod("x1"));
        assertEquals("[method x2, method x4]", x1Dep.toString());

        Object x2Dep = TestUtil.call(ta, "getCalledDecls", project.getMethod("x2"));
        assertEquals("[method x2, method x3, method x4]", x2Dep.toString());

        Object x3Dep = TestUtil.call(ta, "getCalledDecls", project.getMethod("x3"));
        assertEquals("[method x1, method x4]", x3Dep.toString());

        Object x4Dep = TestUtil.call(ta, "getCalledDecls", project.getMethod("x4"));
        assertEquals("[]", x4Dep.toString());

    }

}