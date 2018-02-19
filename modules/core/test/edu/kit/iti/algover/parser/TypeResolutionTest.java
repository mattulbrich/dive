/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */

package edu.kit.iti.algover.parser;

import edu.kit.iti.algover.dafnystructures.DafnyMethod;
import edu.kit.iti.algover.project.Project;
import edu.kit.iti.algover.project.ProjectBuilder;
import edu.kit.iti.algover.util.TreeUtil;
import edu.kit.iti.algover.util.Util;
import junitparams.JUnitParamsRunner;
import junitparams.Parameters;
import org.antlr.runtime.RecognitionException;
import org.junit.Test;
import org.junit.runner.RunWith;

import java.io.IOException;
import java.io.InputStream;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import static org.junit.Assert.*;

@RunWith(JUnitParamsRunner.class)
public class TypeResolutionTest {

    public TypeResolutionTest() {
        super();
    }

    // Different from TestUtil.mockProject!
    private static Project mockProject(DafnyTree tree) throws IOException, DafnyException, DafnyParserException, RecognitionException {
        ProjectBuilder pb = new ProjectBuilder();
        pb.disableNameResolution();
        pb.addDafnyTree("dummy", tree);
        return pb.build();
    }

    public Iterable<Object[]> parametersForTestVisitMethod() throws Exception {
        DafnyTree tree = ParserTest.parseFile(TypeResolutionTest.class.getResourceAsStream("typingTest.dfy"));
        DafnyFileParser.setFilename(tree, "typingTest.dfy");
        Project project = mockProject(tree);
        ArrayList<DafnyException> exceptions = new ArrayList<>();
        ReferenceResolutionVisitor rrr = new ReferenceResolutionVisitor(project, exceptions);
        rrr.visitProject();
        if(!exceptions.isEmpty()) {
            for (DafnyException dafnyException : exceptions) {
                dafnyException.printStackTrace();
            }
            fail("Unexpected exceptions");
        }

        List<Object[]> result = new ArrayList<>();
        for (DafnyMethod method : project.getClass("C").getMethods()) {
            result.add(new Object[] { method.getName(), project });
        }
        // result = Collections.singletonList(new Object[] { "quantifiers", project});
        return result;
    }

    @Test
    @Parameters
    public void testVisitMethod(String method, Project project) throws Exception {
        List<DafnyException> exceptions = new ArrayList<>();
        TypeResolution tr = new TypeResolution(exceptions);
        DafnyMethod m = project.getClass("C").getMethod(method);
        assertNotNull(m);
        m.getRepresentation().accept(tr, null);

        InputStream eis = getClass().getResourceAsStream(method + ".expected.exceptions");
        String[] expectedErrorTrees;
        if (eis == null) {
            expectedErrorTrees = new String[0];
        } else {
            expectedErrorTrees = Util.streamToString(eis).split("\n");
        }

        assertEquals("Number of exceptions", expectedErrorTrees.length, exceptions.size());
        for (int i = 0; i < expectedErrorTrees.length; i++) {
            assertEquals(expectedErrorTrees[i], exceptions.get(i).getTree().toStringTree());
        }

        if(expectedErrorTrees.length == 0) {
            InputStream is = getClass().getResourceAsStream(method + ".expected.typing");
            assertNotNull("missing resource: " + method + ".expected.typing", is);
            String expect = Util.streamToString(is).replaceAll("\\s+", " ").trim();
            String actual = toTypedString(m.getRepresentation()).replaceAll("\\s+", " ").trim();
            assertEquals("Parsing result", expect, actual);
        }
    }

    public static String toTypedString(DafnyTree tree) {
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

    // suspecting a bug
    @Test
    public void testEquality1() {
        {
            DafnyTree tree = new DafnyTree(DafnyParser.GT);
            tree.addChild(new DafnyTree(DafnyParser.INT_LIT, "1"));
            tree.addChild(new DafnyTree(DafnyParser.INT_LIT, "0"));

            List<DafnyException> exceptions = new ArrayList<>();
            tree.accept(new TypeResolution(exceptions), null);

            assertEquals("bool", tree.getExpressionType().toStringTree());
            assertEquals(0, exceptions.size());
        }
        {
            DafnyTree tree = new DafnyTree(DafnyParser.EQ);
            tree.addChild(new DafnyTree(DafnyParser.INT_LIT, "1"));
            tree.addChild(new DafnyTree(DafnyParser.INT_LIT, "0"));

            List<DafnyException> exceptions = new ArrayList<>();
            tree.accept(new TypeResolution(exceptions), null);

            System.out.println(toTypedString(tree));

            assertEquals("bool", tree.getExpressionType().toStringTree());
            assertEquals(0, exceptions.size());
        }
    }
}
