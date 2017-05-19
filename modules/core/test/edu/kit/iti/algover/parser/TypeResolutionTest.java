/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.parser;

import java.io.File;
import java.util.ArrayList;

import org.junit.Test;

import edu.kit.iti.algover.dafnystructures.DafnyTreeToDeclVisitor;
import edu.kit.iti.algover.project.Project;
import edu.kit.iti.algover.project.ProjectBuilder;
import edu.kit.iti.algover.util.TreeUtil;

import static org.junit.Assert.*;

public class TypeResolutionTest {

    class Checker extends DafnyTreeDefaultVisitor<Void, Void> {

        @Override
        public Void visitDefault(DafnyTree t, Void arg) {
            for (DafnyTree child : t.getChildren()) {
                child.accept(this, null);
            }
            return arg;
        }

        @Override
        public Void visitID(DafnyTree t, Void a) {
            switch(t.getParent().getType()) {
            case DafnyParser.VAR:
            case DafnyParser.FIELD:
                return null;
            }

            if(t.getText().startsWith("i_")) {
                assertEquals(DafnyParser.INT, t.getExpressionType().getType());
            }
            if(t.getText().startsWith("b_")) {
                assertEquals(DafnyParser.BOOL, t.getExpressionType().getType());
            }
            if(t.getText().startsWith("c_")) {
                assertEquals(DafnyParser.ID, t.getExpressionType().getType());
                assertEquals("C", t.getExpressionType().getText());
            }
            return a;
        }

        @Override
        public Void visitASSIGN(DafnyTree t, Void a) {
            visitDefault(t, a);
            String type0 = TreeUtil.toTypeString(t.getChild(0).getExpressionType());
            String type1 = TreeUtil.toTypeString(t.getChild(0).getExpressionType());
            if(!type1.equals("*")) {
                // wildcards are allowed
                assertEquals(type0, type1);
            }
            return a;
        }
    }

    @Test
    public void testPositive() throws Exception {
        testTypes("typingTest.dfy");
    }

    private void testTypes(String resource, String... expectedErrorTrees) throws Exception {
        DafnyTree tree = ParserTest.parseFile(getClass().getResourceAsStream(resource));
        Project project = mockProject(tree);
        ArrayList<DafnyException> exceptions = new ArrayList<>();
        ReferenceResolutionVisitor rrr = new ReferenceResolutionVisitor(project, exceptions);
        rrr.visitProject();
        assertTrue(exceptions.isEmpty());

        TypeResolution tr = new TypeResolution(exceptions);
        tr.visitProject(project);
        assertEquals(expectedErrorTrees.length, exceptions.size());
        for (int i = 0; i < expectedErrorTrees.length; i++) {
            assertEquals(expectedErrorTrees[i], exceptions.get(i).getTree().toStringTree());
        }

        tree.accept(new Checker(), null);
    }

    private Project mockProject(DafnyTree tree) {
        ProjectBuilder pb = new ProjectBuilder();
        DafnyTreeToDeclVisitor visitor = new DafnyTreeToDeclVisitor(pb, new File("dummy"));
        visitor.visit("dummy", tree);
        return new Project(pb);
    }
}
