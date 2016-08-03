/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2016 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.symbex;

import java.io.InputStream;
import java.util.List;

import org.junit.Before;
import org.junit.Test;
import static org.junit.Assert.*;

import edu.kit.iti.algover.ProgramDatabase;
import edu.kit.iti.algover.parser.DafnyParser;
import edu.kit.iti.algover.parser.DafnyTree;
import edu.kit.iti.algover.parser.ParserTest;

public class ProgramDatabaseTest {

    private DafnyTree tree;

    @Before
    public void loadTree() throws Exception {
        InputStream stream = getClass().getResourceAsStream("decltest.dfy");
        this.tree = ParserTest.parseFile(stream);
    }

    @Test
    public void testAllDeclarations() {

        List<DafnyTree> result = ProgramDatabase.getAllVariableDeclarations(tree);

        assertEquals(8, result.size());
        for (DafnyTree dafnyTree : result) {
            assertEquals(DafnyParser.VAR, dafnyTree.getType());
        }

    }

}
