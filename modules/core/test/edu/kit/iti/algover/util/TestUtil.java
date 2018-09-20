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
import org.junit.Test;

public class TestUtil {

    /**
     * Adding {@code -Dalgover.verbose=true} to the call of AlgoVer tests
     * makes some test cases to produce more output. If your tests propduce lots
     * of output, you are encouraged to make this output conditional using
     * <pre>
     * if(TestUtil.VERBOSE) {
     *    // output code
     * }
     * </pre>
     * to clutter the standard output less.
     */
    @TestInfrastructure
    public static final boolean VERBOSE =
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

    /**
     * Create a project by parsing the string s as the content of a single dafny
     * file. The filename is set to some bogus dummy filename.
     *
     * @param s the string to parse
     * @return a fresh project with some bogus filename.
     */
    @TestInfrastructure
    public static Project mockProject(String s) throws DafnyParserException, DafnyException, RecognitionException, IOException {
        DafnyTree tree = ParserTest.parseFile(new ByteArrayInputStream(s.getBytes()));
        return mockProject(tree);
    }

    /**
     * Create a project by using a tree (COMPILATION_UNIT) of a single dafny
     * file. The filename is set to some bogus dummy filename.
     *
     * @param tree the dafny tree to work on
     * @return a fresh project with some bogus filename.
     */
    @TestInfrastructure
    public static Project mockProject(DafnyTree tree) throws IOException, DafnyParserException, DafnyException, RecognitionException {
        ProjectBuilder pb = new ProjectBuilder();
        pb.addDafnyTree("dummyFilenameForTesting.dfy", tree);
        return mockProject(pb);
    }

    /**
     * Create a project by using a partially set up project builder
     *
     * @param pb the builder to use
     * @return a fresh project with some bogus filename.
     */
    @TestInfrastructure
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

    /**
     * Set the field of an object even if it is private.
     *
     * Reflection is used. This allows fields to remain private and yet to be
     * tested.
     *
     * @param object the object to change, not null.
     * @param fieldName the name of the field in the dynamic type of object.
     * @param value the value to set to the field.
     */
    @TestInfrastructure
    public static void setField(Object object, String fieldName, Object value) {
        setField(object, object.getClass(), fieldName, value);
    }

    /**
     * Set the field of an object even if it is private.
     *
     * Reflection is used. This allows fields to remain private and yet to be
     * tested.
     *
     * @param object    the object to change, not null.
     * @param inClass   the class in which the field resides.
     * @param fieldName the name of the field in inClass.
     * @param value     the value to set to the field.
     */
    @TestInfrastructure
    public static void setField(Object object, Class<?> inClass, String fieldName, Object value) {
        try {
            Field f = inClass.getDeclaredField(fieldName);
            f.setAccessible(true);
            f.set(object, value);
        } catch(Exception ex) {
            throw new RuntimeException(ex);
        }
    }

    /**
     * Call a method on an object even if it is a private one.
     *
     * @param object     the receiver of the call
     * @param methodName the name of a method in the dynamic type of object
     * @param args       optional arguments of the call
     * @return the result value of the method call.
     */
    @TestInfrastructure
    public static Object call(Object object, String methodName, Object... args) {
        return call(object, object.getClass(), methodName, args);
    }

    /**
     * Call a method on an object even if it is a private one.
     *
     * @param object     the receiver of the call
     * @param inClass    the class in which the method is defined
     * @param methodName the name of a method in inClass
     * @param args       optional arguments of the call
     * @return the result value of the method call.
     */
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

    /**
     * Call a static method, even if it is private.
     *
     * @param inClass    the class in which the method is defined.
     * @param methodName the name of the method
     * @param args       optional arguments
     * @return the result value of the invocation
     */
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
