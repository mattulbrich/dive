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

import edu.kit.iti.algover.parser.PseudoParser.program_return;
import edu.kit.iti.algover.util.TestUtil;

@RunWith(Parameterized.class)
public class ParserTest {

    private static final boolean VERBOSE =
            Boolean.getBoolean("algover.test.verbose");

    @Parameters(name= "{0}")
    public static Iterable<Object[]> data() {
        return Arrays.asList(new Object[][] {
                { "arrayMax" }, { "highdimarrays" }, { "../symbex/symbex" },
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

        PseudoTree t = parseFile(url.openStream());

        if(VERBOSE) {
            // print out the tree
            System.out.println(TestUtil.beautify(t));
        }
    }

    public static PseudoTree parseFile(InputStream stream) throws FileNotFoundException,
            IOException, RecognitionException {

        if(stream == null) {
            throw new NullPointerException();
        }

        ANTLRInputStream input = new ANTLRInputStream(stream);
        PseudoLexer lexer = new PseudoLexer(input);
        // create the buffer of tokens between the lexer and parser
        CommonTokenStream tokens = new CommonTokenStream(lexer);
        // create the parser attached to the token buffer
        PseudoParser parser = new PseudoParser(tokens);
        parser.setTreeAdaptor(new PseudoTree.Adaptor());
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
        PseudoTree t = result.getTree();
        return t;
    }

}
