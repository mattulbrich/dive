/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 *
 */

package edu.kit.iti.algover.dafnystructures;

import edu.kit.iti.algover.parser.DafnyTree;
import edu.kit.iti.algover.parser.ParserTest;
import edu.kit.iti.algover.project.Project;
import edu.kit.iti.algover.util.TestUtil;
import edu.kit.iti.algover.util.Util;
import org.junit.Test;

import java.io.InputStream;
import java.util.Arrays;
import java.util.HashSet;
import java.util.Set;

import static org.junit.Assert.*;

public class CallgraphTest {


    private String[] expectedTarjanCalls = {
        "C.m1 -> [5, 6]",
        "C.m2 -> [11, 12, 13]",
        "C.m3 -> [18]",
        "C.m4 -> []",
        "x1 -> [29, 30]",
        "x2 -> [37, 39, 40]",
        "x3 -> [45, 48]",
        "x4 -> []",
    };

    @Test
    public void testTarjanCalls() throws Exception {

        InputStream stream = getClass().getResourceAsStream("tarjan.dfy");
        DafnyTree fileTree = ParserTest.parseFile(stream);

        // performs type analysis etc:
        Project project = TestUtil.mockProject(fileTree);
        Callgraph graph = project.getCallgraph();

        Set<String> calls = new HashSet<>();
        for (DafnyMethod m : project.getMethods()) {
            calls.add(m.getName() + " -> " +
                    Util.map(graph.getCalls(m), x -> x.getStartToken().getLine()));
        }
        for (DafnyMethod m : project.getClass("C").getMethods()) {
            calls.add("C." + m.getName() + " -> "
                    + Util.map(graph.getCalls(m), x -> x.getStartToken().getLine()));
        }

        Set<String> expectedSet = new HashSet<>(Arrays.asList(expectedTarjanCalls));
        assertEquals(expectedSet, calls);
    }

    private String[] expectedTarjanCallsites = {
            "C.m1 -> [5]",
            "C.m2 -> [6, 11, 18]",
            "C.m3 -> [12]",
            "C.m4 -> [13]",
            "x1 -> [48]",
            "x2 -> [29, 37]",
            "x3 -> [39]",
            "x4 -> [30, 40, 45]",
    };

    @Test
    public void testTarjanCallSites() throws Exception {

        InputStream stream = getClass().getResourceAsStream("tarjan.dfy");
        DafnyTree fileTree = ParserTest.parseFile(stream);

        // performs type analysis etc:
        Project project = TestUtil.mockProject(fileTree);
        Callgraph graph = project.getCallgraph();

        Set<String> calls = new HashSet<>();
        for (DafnyMethod m : project.getMethods()) {
            calls.add(m.getName() + " -> " +
                    Util.map(graph.getCallsites(m), x -> x.getStartToken().getLine()));
        }
        for (DafnyMethod m : project.getClass("C").getMethods()) {
            calls.add("C." + m.getName() + " -> "
                    + Util.map(graph.getCallsites(m), x -> x.getStartToken().getLine()));
        }

        Set<String> expectedSet = new HashSet<>(Arrays.asList(expectedTarjanCallsites));
        assertEquals(expectedSet, calls);
    }



    private String[] expectedCalls = {
           "f1 -> [7, 9]",
           "m1 -> [13, 16, 18]",
           "f2 -> []",
    };

    @Test
    public void testCalls() throws Exception {

        InputStream stream = getClass().getResourceAsStream("callgraph.dfy");
        DafnyTree fileTree = ParserTest.parseFile(stream);

        // performs type analysis etc:
        Project project = TestUtil.mockProject(fileTree);
        Callgraph graph = project.getCallgraph();

        Set<String> calls = new HashSet<>();
        for (DafnyMethod m : project.getMethods()) {
            calls.add(m.getName() + " -> " +
                    Util.map(graph.getCalls(m), x -> x.getStartToken().getLine()));
        }
        for (DafnyFunction m : project.getFunctions()) {
            calls.add(m.getName() + " -> " +
                    Util.map(graph.getCalls(m), x -> x.getStartToken().getLine()));
        }

        Set<String> expectedSet = new HashSet<>(Arrays.asList(expectedCalls));
        assertEquals(expectedSet, calls);
    }

    private String[] expectedCallsites = {
            "m1 -> []",
            // order is: first methods then functions
            "f1 -> [13, 16, 18, 9]",
            "f2 -> [7]",
            };

    @Test
    public void testCallSites() throws Exception {

        InputStream stream = getClass().getResourceAsStream("callgraph.dfy");
        DafnyTree fileTree = ParserTest.parseFile(stream);

        // performs type analysis etc:
        Project project = TestUtil.mockProject(fileTree);
        Callgraph graph = project.getCallgraph();

        Set<String> calls = new HashSet<>();
        for (DafnyMethod m : project.getMethods()) {
            calls.add(m.getName() + " -> " +
                    Util.map(graph.getCallsites(m), x -> x.getStartToken().getLine()));
        }
        for (DafnyFunction m : project.getFunctions()) {
            calls.add(m.getName() + " -> " +
                    Util.map(graph.getCallsites(m), x -> x.getStartToken().getLine()));
        }

        Set<String> expectedSet = new HashSet<>(Arrays.asList(expectedCallsites));
        assertEquals(expectedSet, calls);
    }

}