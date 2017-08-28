/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.util;

import java.io.ByteArrayInputStream;
import java.io.IOException;
import java.io.InputStream;
import java.util.ArrayList;
import java.util.List;
import java.util.function.Function;

import org.antlr.runtime.RecognitionException;

import edu.kit.iti.algover.parser.DafnyException;
import edu.kit.iti.algover.parser.DafnyParserException;
import edu.kit.iti.algover.parser.DafnyTree;
import edu.kit.iti.algover.parser.ReferenceResolutionVisitor;
import edu.kit.iti.algover.parser.TypeResolution;
import edu.kit.iti.algover.project.Project;
import edu.kit.iti.algover.project.ProjectBuilder;

public class TestUtil {

    public static String beautify(DafnyTree tree) {
        return beautify(tree, DafnyTree::toString);
    }

    public static String beautify(DafnyTree tree, Function<DafnyTree, String> printer) {
        StringBuilder sb = new StringBuilder();
        printBeautified(sb, printer, tree, 0);
        return sb.toString();
    }

    private static void printBeautified(StringBuilder buf, Function<DafnyTree, String> printer, DafnyTree tree, int indent) {
        List<DafnyTree> children = tree.getChildren();
        if (children == null || children.isEmpty()) {
            buf.append(printer.apply(tree));
            return;
        }

        newLineIndent(buf, indent);

        if (!tree.isNil()) {
            buf.append("(");
            buf.append(printer.apply(tree));
            buf.append(' ');
        }
        for (int i = 0; children != null && i < children.size(); i++) {
            DafnyTree t = children.get(i);
            if (i > 0) {
                buf.append(' ');
            }
            printBeautified(buf, printer, t, indent+1);
        }
        if (!tree.isNil()) {
            buf.append(")");
        }
    }

    private static void newLineIndent(StringBuilder buf, int indent) {
        buf.append("\n");
        for (int i = 0; i < indent; i++) {
            buf.append(' ');
        }
    }

    public static Project mockProject(DafnyTree tree) throws IOException, DafnyParserException, DafnyException, RecognitionException {
        ProjectBuilder pb = new ProjectBuilder();
        pb.addDafnyTree("dummy", tree);
        Project p = pb.build();

        List<DafnyException> exceptions = new ArrayList<>();

        ReferenceResolutionVisitor refResolver = new ReferenceResolutionVisitor(p, exceptions);
        refResolver.visitProject();

        if(!exceptions.isEmpty()) {
            for (DafnyException dafnyException : exceptions) {
                dafnyException.printStackTrace();
            }
            throw exceptions.get(0);
        }

        TypeResolution typeRes = new TypeResolution(exceptions);
        typeRes.visitProject(p);


        if(!exceptions.isEmpty()) {
            for (DafnyException dafnyException : exceptions) {
                dafnyException.printStackTrace();
            }
            throw exceptions.get(0);
        }

        return p;
    }

    public static InputStream toStream(String string) {
        return new ByteArrayInputStream(string.getBytes());
    }

}
