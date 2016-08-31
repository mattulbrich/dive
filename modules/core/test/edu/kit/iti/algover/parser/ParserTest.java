/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2016 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.parser;

import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.InputStream;
import java.net.URL;
import java.util.Arrays;

import org.antlr.runtime.ANTLRInputStream;
import org.antlr.runtime.CommonTokenStream;
import org.antlr.runtime.RecognitionException;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;

import edu.kit.iti.algover.parser.DafnyParser.program_return;
import edu.kit.iti.algover.util.TestUtil;

@RunWith(Parameterized.class)
public class ParserTest {

    private static final boolean VERBOSE =
            Boolean.getBoolean("algover.test.verbose");

    @Parameters(name= "{0}")
    public static Iterable<Object[]> data() {
        return Arrays.asList(new Object[][] {
                { "arrayMax.dfy" }, { "highdimarrays.dfy" }, { "arrayEdit.dfy" },
                { "../symbex/symbex.dfy" },
                { "arithmetic.dfy" }, { "../util/labelTest.dfy" }, { "../symbex/whileWithAnon.dfy" },
                { "../symbex/havoc.dfy" }, { "../symbex/runtimeAssert.dfy" },
                });
    }

    private final String filename;

    public ParserTest(String filename) {
        this.filename = filename;
    }

    @Test
    public void test() throws Exception {

        URL url = getClass().getResource(filename);

        if(url == null) {
            throw new FileNotFoundException(filename);
        }

        DafnyTree t = parseFile(url.openStream());

        if(VERBOSE) {
            // print out the tree
            System.out.println(TestUtil.beautify(t));
        }
    }

    public static DafnyTree parseFile(InputStream stream) throws FileNotFoundException,
            IOException, RecognitionException {

        if(stream == null) {
            throw new NullPointerException();
        }

        ANTLRInputStream input = new ANTLRInputStream(stream);
        DafnyLexer lexer = new DafnyLexer(input);
        // create the buffer of tokens between the lexer and parser
        CommonTokenStream tokens = new CommonTokenStream(lexer);
        // create the parser attached to the token buffer
        DafnyParser parser = new DafnyParser(tokens);
        parser.setTreeAdaptor(new DafnyTree.Adaptor());
        // launch the parser starting at rule r, get return object
        program_return result;
        try {
            result = parser.program();
        } catch (RecognitionException e) {

            System.err.println("Exception details: " + parser.getErrorMessage(e, parser.getTokenNames()));
            System.err.printf("line %d, token %s%n", e.line, e.token);

            throw e;
        }
        // pull out the tree and cast it
        DafnyTree t = result.getTree();
        return t;
    }

}