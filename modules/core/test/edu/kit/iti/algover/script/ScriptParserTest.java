package edu.kit.iti.algover.script;

import edu.kit.iti.algover.script.ast.ASTNode;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;

import java.io.FileNotFoundException;
import java.io.InputStream;
import java.net.URL;
import java.util.Arrays;

/**
 * Test class for testing the script parser
 */
@RunWith(Parameterized.class)
public class ScriptParserTest {

    private static final boolean VERBOSE = Boolean.getBoolean("algover.test.verbose");
    private final String filename;

    public ScriptParserTest(String filename) {
        this.filename = filename;
    }

        @Parameterized.Parameters(name= "{0}")
        public static Iterable<Object[]> data() {
            return Arrays.asList(new Object[][] {
                    { "project.script" },
            });
        }

        @Test
        public void test() throws Exception {

            URL url = getClass().getResource(filename);

            if(url == null) {
                throw new FileNotFoundException(filename);
            }
            ASTNode t = parseScriptFile(url.openStream());

           /* ScriptTree t = parseFile(url.openStream());

            if(VERBOSE) {
                // print out the tree
                System.out.println(t.toStringTree());
            }*/
        }

    private ASTNode parseScriptFile(InputStream inputStream) {
        if (inputStream == null) {
            throw new NullPointerException();
        }
        return null;

    }

       /* public static ScriptTree parseFile(InputStream stream) throws FileNotFoundException,
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
*/


}
