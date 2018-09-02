/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.util;

import java.io.ByteArrayInputStream;
import java.io.IOException;
import java.io.InputStream;
import java.lang.reflect.Field;
import java.lang.reflect.Method;
import java.lang.reflect.Modifier;
import java.lang.reflect.Parameter;
import java.util.ArrayList;
import java.util.List;
import java.util.function.Function;

import edu.kit.iti.algover.dafnystructures.DafnyMethod;
import edu.kit.iti.algover.dafnystructures.TarjansAlgorithm;
import edu.kit.iti.algover.parser.*;
import edu.kit.iti.algover.proof.Proof;
import edu.kit.iti.algover.proof.ProofNode;
import org.antlr.runtime.ANTLRStringStream;
import org.antlr.runtime.CommonTokenStream;
import org.antlr.runtime.Parser;
import org.antlr.runtime.ParserRuleReturnScope;
import org.antlr.runtime.RecognitionException;

import edu.kit.iti.algover.project.Project;
import edu.kit.iti.algover.project.ProjectBuilder;
import org.hamcrest.BaseMatcher;
import org.hamcrest.Description;
import org.hamcrest.Matcher;

public class TestUtil {

    public static boolean VERBOSE =
            Boolean.getBoolean("algover.verbose");

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

    public static Project mockProject(String s) throws DafnyParserException, DafnyException, RecognitionException, IOException {
        DafnyTree tree = ParserTest.parseFile(new ByteArrayInputStream(s.getBytes()));
        return mockProject(tree);
    }


    public static Project mockProject(DafnyTree tree) throws IOException, DafnyParserException, DafnyException, RecognitionException {
        ProjectBuilder pb = new ProjectBuilder();
        pb.addDafnyTree("dummyFilenameForTesting.dfy", tree);
        return mockProject(pb);
    }

    public static Project mockProject(ProjectBuilder pb) throws DafnyException, DafnyParserException, IOException {
        try {
            Project p = pb.build();
            return p;
        } catch(DafnyException dex) {
            ExceptionDetails.printNiceErrorMessage(dex);
            throw dex;
        }
    }

    public static InputStream toStream(String string) {
        return new ByteArrayInputStream(string.getBytes());
    }

    public static DafnyTree toTree(
            FunctionWithException<DafnyParser,ParserRuleReturnScope,RecognitionException> parserRule,
            String string) throws RecognitionException {
        ANTLRStringStream input = new ANTLRStringStream(string);
        DafnyLexer lexer = new DafnyLexer(input);
        CommonTokenStream tokens = new CommonTokenStream(lexer);

        DafnyParser parser = new DafnyParser(tokens);
        parser.setTreeAdaptor(new DafnyTree.Adaptor());
        parser.setLogicMode(true);
        DafnyTree tree = (DafnyTree) parserRule.apply(parser).getTree();
        return tree;
    }

    public static CharSequence prettyPrintSMT(String smt) {
        StringBuilder sb = new StringBuilder();

        int level = 0;
        for (int i = 0; i < smt.length(); i++) {
            char c = smt.charAt(i);
            if (c == '(') {
                System.out.println();
                System.out.print(Util.duplicate(" ", level));
                level++;
            }
            System.out.print(c);
            if (c == ')') {
                level--;
            }
        }

        return sb;
    }


    public static void setField(Object object, String fieldName, Object value) {
        setField(object, object.getClass(), fieldName, value);
    }

    public static void setField(Object object, Class<?> inClass, String fieldName, Object value) {
        try {
            Field f = inClass.getDeclaredField(fieldName);
            f.setAccessible(true);
            f.set(object, value);
        } catch(Exception ex) {
            throw new RuntimeException(ex);
        }
    }

    public static Object call(Object object, String methodName, Object... args) {
        return call(object, object.getClass(), methodName, args);
    }

    public static Object call(Object object, Class<?> inClass, String methodName, Object... args) {
        try {
            methodName = methodName.intern();
            Method[] ms = inClass.getDeclaredMethods();
            for (Method m : ms) {
                if(m.getName() != methodName || m.getParameterCount() != args.length) {
                    continue;
                }
                for (int i = 0; i < args.length; i++) {
                    Class<?> param = m.getParameterTypes()[i];
                    if(args[i] != null && !param.isAssignableFrom(args[i].getClass())) {
                        continue;
                    }
                }
                m.setAccessible(true);
                return m.invoke(object, args);
            }
            throw new NoSuchMethodException("Not found!");
        } catch(Exception ex) {
            throw new RuntimeException(ex);
        }
    }

    public static Object callStatic(Class<?> inClass, String methodName, Object... args) {
        try {
            methodName = methodName.intern();
            Method[] ms = inClass.getDeclaredMethods();
            for (Method m : ms) {
                if(m.getName() != methodName || m.getParameterCount() != args.length
                        || !Modifier.isStatic(m.getModifiers())) {
                    continue;
                }
                for (int i = 0; i < args.length; i++) {
                    Class<?> param = m.getParameterTypes()[i];
                    if(args[i] != null && !param.isAssignableFrom(args[i].getClass())) {
                        continue;
                    }
                }
                m.setAccessible(true);
                return m.invoke(null, args);
            }
            throw new NoSuchMethodException("Not found!");
        } catch(Exception ex) {
            throw new RuntimeException(ex);
        }
    }


    public static Matcher<Object> isContainedIn(List<?> list) {
        return new BaseMatcher<Object>() {
            @Override
            public boolean matches(Object o) {
                return list.contains(o);
            }

            @Override
            public void describeTo(Description description) {
                description.appendText("not contained in " + list);
            }
        };
    }
}
