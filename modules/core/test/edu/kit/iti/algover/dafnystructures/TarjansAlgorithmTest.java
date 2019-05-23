/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.dafnystructures;

import edu.kit.iti.algover.parser.DafnyException;
import edu.kit.iti.algover.parser.DafnyParserException;
import edu.kit.iti.algover.parser.DafnyTree;
import edu.kit.iti.algover.parser.ParserTest;
import edu.kit.iti.algover.project.Project;
import edu.kit.iti.algover.util.ImmutableList;
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

        DafnyMethod[] x = new DafnyMethod[4];
        String[] gx = new String[4];
        for (int i = 0; i < x.length; i++) {
            x[i] = project.getMethod("x" + (i+1));
            gx[i] = x[i].getRepresentation().getExpressionType().toStringTree();
        }

        DafnyClass c = project.getClass("C");
        DafnyMethod m[] = new DafnyMethod[4];
        String[] gm = new String[4];
        for (int i = 0; i < m.length; i++) {
            m[i] = c.getMethod("m" + (i+1));
            gm[i] = m[i].getRepresentation().getExpressionType().toStringTree();
        }

        // The actual numbers are irrelevant. Their relative equality is important!
        assertEquals("scc_2", gm[0]);
        assertEquals("scc_1", gm[1]);
        assertEquals("scc_1", gm[2]);
        assertEquals("scc_0", gm[3]);

        assertEquals("scc_4", gx[0]);
        assertEquals("scc_4", gx[1]);
        assertEquals("scc_4", gx[2]);
        assertEquals("scc_3", gx[3]);
    }

    @Test
    public void testComputeDecls() throws Exception {
        TarjansAlgorithm ta = new TarjansAlgorithm(project);

        Object x1Dep = TestUtil.call(ta, "getCalledDecls", project.getMethod("x1"));
        ImmutableList<?> x1DepList = ImmutableList.from((Iterable<?>) x1Dep).map(Object::toString).sort();
        assertEquals("[method x2, method x4]", x1DepList.toString());

        Object x2Dep = TestUtil.call(ta, "getCalledDecls", project.getMethod("x2"));
        ImmutableList<?> x2DepList = ImmutableList.from((Iterable<?>) x2Dep).map(Object::toString).sort();
        assertEquals("[method x2, method x3, method x4]", x2DepList.toString());

        Object x3Dep = TestUtil.call(ta, "getCalledDecls", project.getMethod("x3"));
        ImmutableList<?> x3DepList = ImmutableList.from((Iterable<?>) x3Dep).map(Object::toString).sort();
        assertEquals("[method x1, method x4]", x3DepList.toString());

        Object x4Dep = TestUtil.call(ta, "getCalledDecls", project.getMethod("x4"));
        ImmutableList<?> x4DepList = ImmutableList.from((Iterable<?>) x4Dep).map(Object::toString).sort();
        assertEquals("[]", x4DepList.toString());

    }

}