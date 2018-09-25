/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.parser;

import edu.kit.iti.algover.util.TestUtil;
import edu.kit.iti.algover.util.Util;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;

import java.io.ByteArrayInputStream;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.InputStream;
import java.net.URL;
import java.util.Arrays;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

@RunWith(Parameterized.class)
public class ParserTest {

    private static final boolean VERBOSE =
            Boolean.getBoolean("algover.test.verbose");
    private final String filename;

    public ParserTest(String filename) {
        this.filename = filename;
    }

    @Parameters(name= "{0}")
    public static Iterable<Object[]> data() {
        return Arrays.asList(new Object[][] {
                { "arrayMax.dfy" },
                { "highdimarrays.dfy" },
                { "arrayEdit.dfy" },
                { "elseif.dfy" },
                { "wildcards.dfy" },
                { "emptyClass.dfy" },
                { "emptyProgram.dfy" },
                { "../symbex/symbex.dfy" },
                { "arithmetic.dfy" },
                { "../util/labelTest.dfy" },
                { "../symbex/whileWithAnon.dfy" },
                { "../symbex/havoc.dfy" },
                { "../symbex/runtimeAssert.dfy" },
                { "fields.dfy" },
                { "../dafnystructures/declTest.dfy" },
                { "referenceTest.dfy" },
                { "referenceTestWithReftype.dfy" },
                { "reftypes.dfy" },
                { "doubleAccess.dfy" },
                { "faultyReferences.dfy" },
                { "typingTest.dfy" },
                { "full/sumandmax.dfy" },
                { "full/find.dfy" },
                { "full/twoway.dfy" },
                { "full/Problem2-Invert.dfy" },
                { "full/Problem1-SumMax.dfy" },
                { "unqualifiedCallsInExp.dfy" },
                { "letexpressions.dfy" },
                { "typeParameters.dfy" },
                { "../term/builder/sequenterTest.dfy" },
                { "../symbex/noetherTest.dfy" },
                { "../symbex/crossClass.dfy" },
                { "vars.dfy" },
                { "newCommand.dfy" },
                { "methodCalls.dfy" },
                { "schwarz1.dfy" },
                });
    }

    private static String formatTree(DafnyTree tree) {
        return tree.getText() +
                String.format("[%s-%s]",
                        tree.getStartToken().getText(), tree.getStopToken().getText());
    }

    public static DafnyTree parseFile(InputStream stream) throws DafnyParserException, IOException {
        return parseFile(stream, null);
    }

    public static DafnyTree parseFile(InputStream stream, String filename) throws DafnyParserException, IOException {

        if (stream == null) {
            throw new NullPointerException();
        }

        DafnyTree result = DafnyFileParser.parse(stream, true);
        DafnyFileParser.setFilename(result, filename);

        return result;
    }

    public static void main(String[] args) throws Exception {
        DafnyTree t;
        if (args.length > 0) {
            t = parseFile(new FileInputStream(args[0]));
        } else {
            t = parseFile(System.in);
        }
        // w/o boundaries: remove formatTree parameter
        System.out.println(TestUtil.beautify(t, ParserTest::formatTree));
    }

    @Test
    public void test() throws Exception {

        URL url = getClass().getResource(filename);

        if(url == null) {
            throw new FileNotFoundException(filename);
        }

        DafnyTree t = parseFile(url.openStream(), filename);

        if(VERBOSE) {
            // print out the tree
            System.out.println(TestUtil.beautify(t));
        }

        URL expected = getClass().getResource(filename + ".expected");
        if(expected != null) {
            String expect = Util.streamToString(expected.openStream()).replaceAll("\\s+", " ").trim();
            String actual = t.toStringTree().replaceAll("\\s+", " ").trim();
            // assertEquals("For inspection", Util.streamToString(expected.openStream()), TestUtil.beautify(t));
            assertEquals("Parsing result", expect, actual);
        }

        expected = getClass().getResource(filename + ".expected-boundaries");
        if(expected != null) {
            String expect = Util.streamToString(expected.openStream()).replaceAll("\\s+", " ").trim();
            String actual = TestUtil.beautify(t, ParserTest::formatTree).replaceAll("\\s+", " ").trim();
            // assertEquals("For inspection", Util.streamToString(expected.openStream()), TestUtil.beautify(t));
            assertEquals("Parsing result", expect, actual);
        }
    }

}
