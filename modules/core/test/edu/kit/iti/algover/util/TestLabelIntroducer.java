/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2016 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.util;


// import static org.junit.Assert.*;

import static org.junit.Assert.*;

import java.io.FileNotFoundException;
import java.net.URL;
import java.util.ArrayList;
import java.util.List;

import org.junit.Test;

import edu.kit.iti.algover.parser.DafnyParser;
import edu.kit.iti.algover.parser.DafnyTree;
import edu.kit.iti.algover.parser.ParserTest;

public class TestLabelIntroducer {

    private static final boolean VERBOSE = true;

    @Test
    public void test() throws Exception {

        String filename = "labelTest.dfy";
        URL url = getClass().getResource(filename);
        if(url == null) {
            throw new FileNotFoundException(filename);
        }

        DafnyTree t = ParserTest.parseFile(url.openStream());

        if(VERBOSE) {
            System.out.println(Debug.prettyPrint(t.toStringTree()));
        }

        LabelIntroducer.visit(t);

        if(VERBOSE) {
            System.out.println(Debug.prettyPrint(t.toStringTree()));
        }

        List<DafnyTree> invariants = new ArrayList<>();
        collect(t, DafnyParser.INVARIANT, invariants);

        assertEquals(3, invariants.size());
        assertEquals("#1", invariants.get(0).getFirstChildWithType(DafnyParser.LABEL).getChild(0).getText());
        assertEquals("withLabel", invariants.get(1).getFirstChildWithType(DafnyParser.LABEL).getChild(0).getText());
        assertEquals("#3", invariants.get(2).getFirstChildWithType(DafnyParser.LABEL).getChild(0).getText());

    }

    private void collect(DafnyTree t, int type, List<DafnyTree> result) {
        if(t.getType() == type) {
            result.add(t);
        }

        List<DafnyTree> children = t.getChildren();
        if(children != null) {
            for (DafnyTree child : children) {
                collect(child, type, result);
            }
        }
    }

}
