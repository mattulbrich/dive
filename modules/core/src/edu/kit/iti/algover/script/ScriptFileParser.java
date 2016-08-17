package edu.kit.iti.algover.script;


import org.antlr.runtime.ANTLRInputStream;
import org.antlr.runtime.CommonTokenStream;
import org.antlr.runtime.RecognitionException;
import org.antlr.runtime.tree.CommonTree;


import java.io.File;
import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStream;

/**
 * Created by sarah on 8/16/16.
 */
public class ScriptFileParser {

    private ScriptFileParser() {
        throw new Error();
    }

    public static ScriptTree parse(File file) throws IOException, RecognitionException {
        return parse(new FileInputStream(file));
    }

    public static ScriptTree parse(InputStream stream) throws RecognitionException, IOException {

        // create stream and lexer
        ANTLRInputStream input = new ANTLRInputStream(stream);
        ScriptLexer lexer = new ScriptLexer(input);

        // create the buffer of tokens between the lexer and parser
        CommonTokenStream tokens = new CommonTokenStream(lexer);

        // create the parser attached to the token buffer
        ScriptParser parser = new ScriptParser(tokens);
        ScriptTree.Adaptor adaptor = new ScriptTree.Adaptor();
        parser.setTreeAdaptor(adaptor);

        // launch the parser starting at rule preamble, return result
        ScriptParser.preamble_return result;
        result = parser.preamble();

        // pull out the tree and cast it
        ScriptTree t = result.getTree();

        return t;
    }

}
