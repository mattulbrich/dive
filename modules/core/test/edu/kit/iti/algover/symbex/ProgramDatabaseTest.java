/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2016 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.symbex;

import java.io.IOException;
import java.io.InputStream;
import java.util.Collection;
import java.util.List;

import edu.kit.iti.algover.dafnystructures.DafnyMethod;
import edu.kit.iti.algover.parser.DafnyException;
import edu.kit.iti.algover.parser.DafnyParserException;
import edu.kit.iti.algover.project.Project;
import edu.kit.iti.algover.util.TestUtil;
import org.antlr.runtime.RecognitionException;
import org.junit.Before;
import org.junit.Test;
import static org.junit.Assert.*;

import edu.kit.iti.algover.ProgramDatabase;
import edu.kit.iti.algover.parser.DafnyParser;
import edu.kit.iti.algover.parser.DafnyTree;
import edu.kit.iti.algover.parser.ParserTest;

public class ProgramDatabaseTest {

    @Test
    public void testAllDeclarations() throws IOException, DafnyParserException {
        InputStream stream = getClass().getResourceAsStream("decltest.dfy");
        DafnyTree tree = ParserTest.parseFile(stream);

        List<DafnyTree> result = ProgramDatabase.getAllVariableDeclarations(tree);

        assertEquals(8, result.size());
        for (DafnyTree dafnyTree : result) {
            assertEquals(DafnyParser.VAR, dafnyTree.getType());
        }

    }

    @Test
    public void testStrictlyPureCheck() throws Exception {
        InputStream stream = getClass().getResourceAsStream("strictlyPureTest.dfy");
        DafnyTree fileTree = ParserTest.parseFile(stream);
        Project project = TestUtil.mockProject(fileTree);

        Collection<DafnyMethod> methods = project.getClass("C").getMethods();
        for (DafnyMethod method : methods) {
            boolean pure = ProgramDatabase.isStrictlyPure(method.getRepresentation());
            assertEquals(method.getName(), method.getName().startsWith("pure"), pure);
        }
    }

}
