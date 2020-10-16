/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.util;

import java.io.BufferedReader;
import java.io.ByteArrayInputStream;
import java.io.File;
import java.io.FileFilter;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.io.InputStream;
import java.lang.reflect.Field;
import java.lang.reflect.Method;
import java.lang.reflect.Modifier;
import java.net.MalformedURLException;
import java.net.URL;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Enumeration;
import java.util.List;
import java.util.function.Function;

import edu.kit.iti.algover.nuscript.ScriptsTest;
import edu.kit.iti.algover.parser.*;
import org.antlr.runtime.ANTLRStringStream;
import org.antlr.runtime.CommonTokenStream;
import org.antlr.runtime.ParserRuleReturnScope;
import org.antlr.runtime.RecognitionException;

import edu.kit.iti.algover.project.Project;
import edu.kit.iti.algover.project.ProjectBuilder;
import org.hamcrest.BaseMatcher;
import org.hamcrest.Description;
import org.hamcrest.Matcher;
import org.hamcrest.TypeSafeMatcher;
import org.junit.Assert;

import static org.junit.Assert.*;

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
            Boolean.getBoolean("dive.verbose");

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
    @TestInfrastructure
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
    @TestInfrastructure
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


    public static Matcher<Object> isContainedIn(Collection<?> list) {
        return new BaseMatcher<Object>() {
            @Override
            public boolean matches(Object o) {
                return list.contains(o);
            }

            @Override
            public void describeTo(Description description) {
                description.appendText("contained in " + list);
            }
        };
    }

    public static <E> TypeSafeMatcher<Collection<E>> contains(E o) {
        return new TypeSafeMatcher<Collection<E>>() {
            @Override
            protected boolean matchesSafely(Collection<E> coll) {
                return coll.contains(o);
            }

            @Override
            public void describeTo(Description description) {
                description.appendText("contains " + o);
            }
        };
    }

    public static Matcher<Collection<?>> isEmpty() {
        return new BaseMatcher<Collection<?>>() {
            @Override
            public boolean matches(Object o) {
                return ((Collection)o).isEmpty();
            }

            @Override
            public void describeTo(Description description) {
                description.appendText("is empty");
            }
        };
    }

    @TestInfrastructure
    public static Project emptyProject() {
        try {
            return mockProject("");
        } catch (Exception e) {
            // Really should not happen ...
            throw new RuntimeException(e);
        }
    }

    @TestInfrastructure
    public static List<URL> getResourcesIn(String path, String suffix, boolean deep) throws IOException {
        assert path != null : "Null resource received!";
        Enumeration<URL> urls = ClassLoader.getSystemResources(path);
        List<URL> result = new ArrayList<>();
        while (urls.hasMoreElements()) {
            URL url = urls.nextElement();
            if(url.getProtocol().equals("file")) {
                result.addAll(getResourcesIn(new File(url.getFile()), suffix, deep));
            }
        }
        return result;
    }

    private static List<URL> getResourcesIn(File resource, String suffix, boolean deep) throws MalformedURLException {
        FileFilter filter = x -> x.getName().endsWith("." + suffix);

        List<URL> children = new ArrayList<>();
        for (File f : resource.listFiles(filter)) {
            children.add(f.toURI().toURL());
        }

        if (deep) {
            for (File d : resource.listFiles(File::isDirectory)) {
                children.addAll(getResourcesIn(d, suffix, deep));
            }
        }

        return children;
    }

    public static void assertSameTextFiles(File expected, File actual) throws IOException {

        int line = 1;
        try(BufferedReader r1 = new BufferedReader(new FileReader(expected));
            BufferedReader r2 = new BufferedReader(new FileReader(actual))) {

            while(true) {
                String line1 = r1.readLine();
                String line2 = r2.readLine();

                if (line1 == null && line2 == null) {
                    // both at end.
                    return;
                }

                if (line1 == null) {
                    fail("Actual file has more lines then expected (" + line + ").");
                }

                if (line1 == null) {
                    fail("Actual file has fewer lines then expected (" + line + ").");
                }

                assertEquals("line " + line + " differs", line1, line2);
                line ++;
            }
        }
    }

    /**
     * Store the parameter string into a temporary file. The filename gets the
     * appoointed file name extension.
     *
     * The file must be deleted manually.
     *
     * @param string content
     * @param extension file name extension
     * @return name of the temporary file
     */
    public static File stringToTempFile(String string, String extension) throws IOException {
        File temp = File.createTempFile("dive", extension);
        try (FileWriter fw = new FileWriter(temp)) {
            fw.write(string);
        }
        return temp;
    }

    @TestInfrastructure
    public static void assertNoException(List<Exception> failures) {
        if (!failures.isEmpty()) {
            for (Exception failure : failures) {
                failure.printStackTrace();
            }
            Assert.fail("Unexpected exception!");
        }
    }

    @TestInfrastructure
    public static String resourceAsString(Class<?> clss, String resource) throws IOException {
        InputStream is = clss.getResourceAsStream(resource);
        if (is == null) {
            throw new FileNotFoundException("Resource " + resource + " not found");
        }
        return Util.streamToString(is);
    }
}
