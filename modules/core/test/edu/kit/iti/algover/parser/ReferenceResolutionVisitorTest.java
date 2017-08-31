/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */

package edu.kit.iti.algover.parser;

import edu.kit.iti.algover.project.Project;
import edu.kit.iti.algover.project.ProjectBuilder;
import edu.kit.iti.algover.util.TestUtil;
import org.junit.Test;

import java.util.ArrayList;
import java.util.List;

import static org.junit.Assert.*;

public class ReferenceResolutionVisitorTest {

    @Test
    public void testWithoutReftype() throws Exception {
        test("referenceTest.dfy");
    }

    @Test
    public void testWithReftype() throws Exception {
        test("referenceTestWithReftype.dfy");
    }

    @Test
    public void testFaulty() throws Exception {
        DafnyTree tree = ParserTest.parseFile(getClass().getResourceAsStream("faultyReferences.dfy"));
        ProjectBuilder pb = new ProjectBuilder();
        pb.addDafnyTree("dummy", tree);
        Project project = pb.build();

        ReferenceResolutionVisitor rrv = new ReferenceResolutionVisitor(project, new ArrayList<>());
        rrv.visitProject();


        String[] errors = {
                "(FIELD_ACCESS c df)",
                "(FIELD_ACCESS c df)",
                "(CALL md c (ARGS c))",
                "(FIELD_ACCESS d cf)",
                "(FIELD_ACCESS d cf)",
                "(CALL mc d (ARGS d))",
                "(var a Unknown)",
                "(FIELD_ACCESS a f)",
                "(== local 0)",
        };

        List<DafnyException> exceptions = rrv.getExceptions();
        for (int i = 0; i < errors.length; i++) {
            // exceptions.get(i).printStackTrace();
            assertEquals(errors[i], exceptions.get(i).getTree().getParent().toStringTree());
        }

        assertEquals(errors.length, exceptions.size());
    }

    private void test(String resourceName) throws Exception {

        DafnyTree tree = ParserTest.parseFile(getClass().getResourceAsStream(resourceName));
        DafnyFileParser.setFilename(tree, resourceName);

        TestUtil.mockProject(tree);

        tree.accept(new CheckVisitor(), null);

    }

    private class CheckVisitor extends DafnyTreeDefaultVisitor<Void, Void> {
        @Override
        public Void visitDefault(DafnyTree t, Void arg) {
            for (DafnyTree child : t.getChildren()) {
                child.accept(this, null);
            }
            return null;
        }

        @Override
        public Void visitID(DafnyTree t, Void a) {
            String name = t.getText();

            switch (t.getParent().getType()) {
                case DafnyParser.METHOD:
                case DafnyParser.FUNCTION:
                case DafnyParser.VAR:
                case DafnyParser.CLASS:
                case DafnyParser.FIELD:
                case DafnyParser.ALL:
                case DafnyParser.EX:
                case DafnyParser.LABEL:
                    return null;
            }

            DafnyTree ref = t.getDeclarationReference();
            assertNotNull(t + " has no ref", ref);
            if (name.startsWith("l_")) {
                assertEquals(DafnyParser.VAR, ref.getType());
                assertEquals(name, ref.getChild(0).getText());
            } else if (name.startsWith("fl_")) {
                assertEquals(DafnyParser.FIELD, ref.getType());
                assertEquals(name, ref.getChild(0).getText());
            } else if (name.startsWith("m_")) {
                assertEquals(DafnyParser.METHOD, ref.getType());
                assertEquals(name, ref.getChild(0).getText());
            } else if (name.startsWith("f_")) {
                assertEquals(DafnyParser.FUNCTION, ref.getType());
                assertEquals(name, ref.getChild(0).getText());
            } else if (name.startsWith("p_")) {
                assertEquals(DafnyParser.VAR, ref.getType());
                assertEquals(name, ref.getChild(0).getText());
            } else if (name.startsWith("vx_")) {
                assertEquals(DafnyParser.EX, ref.getType());
                assertEquals(name, ref.getChild(0).getText());
            } else if (name.startsWith("va_")) {
                assertEquals(DafnyParser.ALL, ref.getType());
                assertEquals(name, ref.getChild(0).getText());
            } else if (name.startsWith("C_")) {
                assertEquals(DafnyParser.CLASS, ref.getType());
                assertEquals(name, ref.getChild(0).getText());
            } else {
                fail("Unsupported identifier " + name);
            }
            return null;
        }
    }

}
