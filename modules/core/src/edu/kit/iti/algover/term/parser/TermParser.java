/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.term.parser;

import java.util.HashMap;

import org.antlr.runtime.ANTLRStringStream;
import org.antlr.runtime.CommonTokenStream;
import org.antlr.runtime.RecognitionException;

import edu.kit.iti.algover.data.SymbolTable;
import edu.kit.iti.algover.parser.DafnyException;
import edu.kit.iti.algover.parser.DafnyLexer;
import edu.kit.iti.algover.parser.DafnyParser;
import edu.kit.iti.algover.parser.DafnyParser.expression_only_return;
import edu.kit.iti.algover.parser.DafnyParserException;
import edu.kit.iti.algover.parser.DafnyTree;
import edu.kit.iti.algover.parser.SyntacticSugarVistor;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.term.VariableTerm;
import edu.kit.iti.algover.term.builder.TreeTermTranslator;
import edu.kit.iti.algover.util.HistoryMap;
import nonnull.NonNull;

/**
 * The class TermParser wraps a {@link DafnyParser} and a
 * {@link TreeTermTranslator} to produce a {@link Term} from a string.
 * Resolution of symbols is done via a {@link SymbolTable}.
 *
 * Exceptions are consolidated into {@link DafnyException}s.
 *
 * @author mattias ulbrich
 */
public class TermParser {

    /**
     * The symbol table used by the {@link TreeTermTranslator}.
     */
    private final @NonNull SymbolTable symbols;

    /**
     * Instantiates a new term parser.
     *
     * @param symbols the known symbols for lookup
     */
    public TermParser(@NonNull SymbolTable symbols) {
        this.symbols = symbols;
    }

    /**
     * Parse a string to a {@link Term}.
     *
     * @param symbols
     *            the known symbols as lookup table
     * @param string
     *            the string to parse
     * @return the corresponding term resulting from parsing
     * @throws DafnyParserException
     *             if the term was illegally formed. The exception contains a
     *             reference to the erring part of the tree
     */
    public static Term parse(@NonNull SymbolTable symbols, @NonNull String string) throws DafnyParserException {
        TermParser tp = new TermParser(symbols);
        return tp.parse(string);
    }

    /**
     * Parses a string to a {@link Term}.
     *
     * @param string
     *            the string to parse
     * @return the corresponding term resulting from parsing
     * @throws DafnyParserException
     *             if the term was illegally formed. The exception contains a
     *             reference to the erring part of the tree
     */
    public Term parse(String string) throws DafnyParserException {

        // create stream and lexer
        ANTLRStringStream input = new ANTLRStringStream(string);
        DafnyLexer lexer = new DafnyLexer(input);

        // create the buffer of tokens between the lexer and parser
        CommonTokenStream tokens = new CommonTokenStream(lexer);

        // create the parser attached to the token buffer
        DafnyParser parser = new DafnyParser(tokens);
        parser.setTreeAdaptor(new DafnyTree.Adaptor());
        parser.setLogicMode(true);

        // launch the parser starting at rule r, get return object
        expression_only_return result;
        try {
            result = parser.expression_only();
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

        // syntactic desugaring
        SyntacticSugarVistor.visit(t);

        return toTerm(t, new HistoryMap<>(new HashMap<>()));
    }

    /*
     * translate a parse tree into a Term.
     */
    private Term toTerm(DafnyTree t, HistoryMap<String, VariableTerm> boundVariables) throws DafnyParserException {

        try {
            TreeTermTranslator ttt = new TreeTermTranslator(symbols);
            return ttt.build(t);
        } catch(Exception e) {
            DafnyParserException lex = new DafnyParserException(e);
            lex.setLine(t.getLine());
            lex.setColumn(t.getCharPositionInLine());
            lex.setLength(t.getText().length());
            throw lex;
        }
    }
}
