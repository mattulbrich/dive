/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.parser;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.InputStream;
import java.net.URL;
import java.util.ArrayList;
import java.util.List;

import org.antlr.runtime.RecognitionException;
import org.antlr.runtime.tree.Tree;
import org.junit.Before;
import org.junit.BeforeClass;
import org.junit.Test;

import edu.kit.iti.algover.dafnystructures.DafnyMethod;
import edu.kit.iti.algover.dafnystructures.DafnyTreeToDeclVisitor;
import edu.kit.iti.algover.project.Project;
import edu.kit.iti.algover.project.ProjectBuilder;
import edu.kit.iti.algover.util.TreeUtil;
import edu.kit.iti.algover.util.Util;

import static org.junit.Assert.*;

public class TypeResolutionTest {

    private Project project;

    @Before
    public void setup() throws FileNotFoundException, IOException, RecognitionException {
        if(project == null) {
            DafnyTree tree = ParserTest.parseFile(getClass().getResourceAsStream("typingTest.dfy"));
            project = mockProject(tree);
            ArrayList<DafnyException> exceptions = new ArrayList<>();
            ReferenceResolutionVisitor rrr = new ReferenceResolutionVisitor(project, exceptions);
            rrr.visitProject();
            assertTrue(exceptions.isEmpty());
        }
    }

    @Test
    public void testPositive() throws Exception {
        testMethod("testAssignments");
    }

    private void testMethod(String method, String... expectedErrorTrees) throws Exception {
        List<DafnyException> exceptions = new ArrayList<>();
        TypeResolution tr = new TypeResolution(exceptions );
        DafnyMethod m = project.getClass("C").getMethod(method);
        assertNotNull(m);
        m.getRepresentation().accept(tr, null);
        assertEquals(expectedErrorTrees.length, exceptions.size());
        for (int i = 0; i < expectedErrorTrees.length; i++) {
            assertEquals(expectedErrorTrees[i], exceptions.get(i).getTree().toStringTree());
        }

        InputStream is = getClass().getResourceAsStream(method + ".expected.typing");
        if(is != null) {
            String expect = Util.streamToString(is).replaceAll("\\s+", " ").trim();
            String actual = toTypedString(m.getRepresentation()).replaceAll("\\s+", " ").trim();
            assertEquals("Parsing result", expect, actual);
        }
    }

    private String toTypedString(DafnyTree tree) {
        List<DafnyTree> children = tree.getChildren();
        StringBuilder buf = new StringBuilder();
        if (children == null || children.isEmpty()) {
            buf.append(tree.toString());
        } else {
            if (!tree.isNil()) {
                buf.append("(");
                buf.append(tree.toString());
                buf.append(' ');
            }
            for (int i = 0; children != null && i < children.size(); i++) {
                DafnyTree t = children.get(i);
                if (i > 0) {
                    buf.append(' ');
                }
                buf.append(toTypedString(t));
            }
            if (!tree.isNil()) {
                buf.append(")");
            }
        }
        DafnyTree ty = tree.getExpressionType();
        if (ty != null) {
            buf.append("[");
            buf.append(TreeUtil.toTypeString(ty));
            buf.append("]");
        }
        return buf.toString();
    }

    private Project mockProject(DafnyTree tree) {
        ProjectBuilder pb = new ProjectBuilder();
        DafnyTreeToDeclVisitor visitor = new DafnyTreeToDeclVisitor(pb, new File("dummy"));
        visitor.visit("dummy", tree);
        return new Project(pb);
    }
}
