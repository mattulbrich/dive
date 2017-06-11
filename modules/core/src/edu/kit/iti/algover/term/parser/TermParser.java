/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.term.parser;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;

import org.antlr.runtime.ANTLRStringStream;
import org.antlr.runtime.CommonTokenStream;
import org.antlr.runtime.RecognitionException;

import edu.kit.iti.algover.data.SymbolTable;
import edu.kit.iti.algover.parser.DafnyLexer;
import edu.kit.iti.algover.parser.DafnyParser;
import edu.kit.iti.algover.parser.DafnyParser.expression_only_return;
import edu.kit.iti.algover.parser.DafnyParserException;
import edu.kit.iti.algover.parser.DafnyTree;
import edu.kit.iti.algover.term.ApplTerm;
import edu.kit.iti.algover.term.FunctionSymbol;
import edu.kit.iti.algover.term.QuantTerm;
import edu.kit.iti.algover.term.QuantTerm.Quantifier;
import edu.kit.iti.algover.term.Sort;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.term.VariableTerm;
import edu.kit.iti.algover.term.builder.TermBuildException;
import edu.kit.iti.algover.term.builder.TermBuilder;
import edu.kit.iti.algover.term.builder.TreeTermTranslator;
import edu.kit.iti.algover.util.HistoryMap;

public class TermParser {

    private final TermBuilder tb;
    private final SymbolTable symbols;

    public TermParser(SymbolTable symbols) {
        this.symbols = symbols;
        this.tb = new TermBuilder(symbols);
    }

    public static Term parse(SymbolTable symbols, String string) throws DafnyParserException {
        TermParser tp = new TermParser(symbols);
        return tp.parse(string);
    }

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

        return toTerm(t, new HistoryMap<>(new HashMap<>()));
    }

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
