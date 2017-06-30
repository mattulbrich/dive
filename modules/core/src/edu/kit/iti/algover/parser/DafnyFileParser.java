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

import org.antlr.runtime.ANTLRInputStream;
import org.antlr.runtime.CommonTokenStream;
import org.antlr.runtime.RecognitionException;

import edu.kit.iti.algover.parser.DafnyParser.program_return;

/**
 * A collection of static methods that can be used to access the DafnyParser.
 *
 * @see DafnyParser.g
 */
public final class DafnyFileParser {

    private DafnyFileParser() {
        throw new Error();
    }

    /**
     * Parses a file into an AST.
     *
     * The filename of <code>file</code> is set as filename in the AST.
     *
     * @param file
     *            the file to parse, not <code>null</code>
     * @return the freshly parsed AST for the file
     * @throws IOException
     *             Signals that an I/O exception has occurred.
     * @throws DafnyParserException
     *             Signals that a parser exception has occurred. The filename is
     *             added to the exception here.
     */
    public static DafnyTree parse(File file) throws IOException, DafnyParserException {
        try {
            DafnyTree tree = parse(new FileInputStream(file));
            setFilename(tree, file.getPath());
            return tree;
        } catch (DafnyParserException e) {
            e.setFilename(file.toString());
            throw e;
        }
    }

    /**
     * Sets the filename in an AST.
     *
     * Recursively applies to children of the given node.
     *
     * @param tree
     *            the tree to visit
     * @param filename
     *            the filename to set.
     */
    public static void setFilename(DafnyTree tree, String filename) {
        tree.setFilename(filename);
        for (DafnyTree child : tree.getChildren()) {
            setFilename(child, filename);
        }
    }

    /**
     * Parses a stream into an AST.
     *
     * The filename remains unset in the result.
     *
     * @param stream
     *            the input stream to parse, not <code>null</code>
     * @return the freshly parsed AST for the file
     * @throws IOException
     *             Signals that an I/O exception has occurred.
     * @throws DafnyParserException
     *             Signals that a parser exception has occurred. The fields in
     *             the exception are filled with information from the parser.
     */
    public static DafnyTree parse(InputStream stream) throws DafnyParserException, IOException {
        return parse(stream, false);
    }

    /**
     * Parses a stream into an AST.
     *
     * The filename remains unset in the result.
     *
     * This parser can be set into logic mode (mainly for debugging purposes)
     * which allows parsing of internal logic sybmols as well.
     *
     * @param stream
     *            the input stream to parse, not <code>null</code>
     * @param allowLogic
     *            if <code>true</code> then internal identifiers like
     *            <code>$identifier</code> are supported by the parser
     * @return the freshly parsed AST for the file
     * @throws IOException
     *             Signals that an I/O exception has occurred.
     * @throws DafnyParserException
     *             Signals that a parser exception has occurred. The fields in
     *             the exception are filled with information from the parser.
     */
    public static DafnyTree parse(InputStream stream, boolean allowLogic) throws DafnyParserException, IOException {

        // create stream and lexer
        ANTLRInputStream input = new ANTLRInputStream(stream);
        DafnyLexer lexer = new DafnyLexer(input);

        // create the buffer of tokens between the lexer and parser
        CommonTokenStream tokens = new CommonTokenStream(lexer);

        // create the parser attached to the token buffer
        DafnyParser parser = new DafnyParser(tokens);
        parser.setTreeAdaptor(new DafnyTree.Adaptor());
        parser.setLogicMode(allowLogic);

        // launch the parser starting at rule r, get return object
        program_return result;
        try {
            result = parser.program();
        } catch (RecognitionException e) {
            String msg = parser.getErrorMessage(e, DafnyParser.tokenNames);
            DafnyParserException lex = new DafnyParserException(msg, e);
            lex.setLine(e.line);
            lex.setColumn(e.charPositionInLine);
            if (e.token != null) {
                lex.setLength(e.token.getText().length());
            }
            throw lex;
        }

        // pull out the tree and cast it
        DafnyTree t = result.getTree();
        return t;
    }

}
