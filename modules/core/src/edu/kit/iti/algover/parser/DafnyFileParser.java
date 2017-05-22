/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.parser;

import java.io.File;
import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStream;
import java.util.List;

import org.antlr.runtime.ANTLRInputStream;
import org.antlr.runtime.CommonTokenStream;
import org.antlr.runtime.RecognitionException;

import edu.kit.iti.algover.parser.DafnyParser.program_return;


public class DafnyFileParser {

    private DafnyFileParser() {
        throw new Error();
    }

    public static DafnyTree parse(File file) throws IOException, RecognitionException {
        DafnyTree tree = parse(new FileInputStream(file));
        setFilename(tree, file.getPath());
        return tree;
    }

    public static void setFilename(DafnyTree tree, String filename) {
        tree.setFilename(filename);
        for (DafnyTree child : tree.getChildren()) {
            setFilename(child, filename);
        }
    }

    public static DafnyTree parse(InputStream stream) throws RecognitionException, IOException {

        // create stream and lexer
        ANTLRInputStream input = new ANTLRInputStream(stream);
        DafnyLexer lexer = new DafnyLexer(input);

        // create the buffer of tokens between the lexer and parser
        CommonTokenStream tokens = new CommonTokenStream(lexer);

        // create the parser attached to the token buffer
        DafnyParser parser = new DafnyParser(tokens);
        parser.setTreeAdaptor(new DafnyTree.Adaptor());

        // launch the parser starting at rule r, get return object
        program_return result;
        result = parser.program();

        // pull out the tree and cast it
        DafnyTree t = result.getTree();
        return t;
    }

}
