package edu.kit.iti.algover.script;

import edu.kit.iti.algover.util.TestUtil;
import org.antlr.runtime.ANTLRInputStream;
import org.antlr.runtime.CommonTokenStream;
import org.antlr.runtime.RecognitionException;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;

import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.InputStream;
import java.net.URL;
import java.util.Arrays;

/**
 * Created by sarah on 8/18/16.
 */
@RunWith(Parameterized.class)
public class ScriptParserTest {





        private static final boolean VERBOSE =
                Boolean.getBoolean("algover.test.verbose");

        @Parameterized.Parameters(name= "{0}")
        public static Iterable<Object[]> data() {
            return Arrays.asList(new Object[][] {
                    { "project.script" },
            });
        }

        private final String filename;

        public ScriptParserTest(String filename) {
            this.filename = filename;
        }

        @Test
        public void test() throws Exception {

            URL url = getClass().getResource(filename);

            if(url == null) {
                throw new FileNotFoundException(filename);
            }

            ScriptTree t = parseFile(url.openStream());

            if(VERBOSE) {
                // print out the tree
                System.out.println(t.toStringTree());
            }
        }

        public static ScriptTree parseFile(InputStream stream) throws FileNotFoundException,
                IOException, RecognitionException {

            if(stream == null) {
                throw new NullPointerException();
            }

            ANTLRInputStream input = new ANTLRInputStream(stream);
            ScriptLexer lexer = new ScriptLexer(input);
            // create the buffer of tokens between the lexer and parser
            CommonTokenStream tokens = new CommonTokenStream(lexer);
            // create the parser attached to the token buffer
            ScriptParser parser = new ScriptParser(tokens);
            parser.setTreeAdaptor(new ScriptTree.Adaptor());

             // launch the parser starting at rule preamble, return result
            ScriptParser.preamble_return result;



            try {
                result = parser.preamble();


            } catch (RecognitionException e) {

                System.err.println("Exception details: " + parser.getErrorMessage(e, parser.getTokenNames()));
                System.err.printf("line %d, token %s%n", e.line, e.token);

                throw e;
            }
            // pull out the tree and cast it

            // pull out the tree and cast it
            ScriptTree t = result.getTree();

            return t;

        }



}
