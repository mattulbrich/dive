/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.term.parser;

import java.util.*;

import edu.kit.iti.algover.dafnystructures.DafnyFile;
import edu.kit.iti.algover.proof.ProofFormula;
import edu.kit.iti.algover.term.Sequent;
import edu.kit.iti.algover.term.builder.TermBuildException;
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
     * Parse a string to a {@link Sequent}.
     *
     * @param symbols
     *            the known symbols as lookup table
     * @param string
     *            the string to parse
     * @return the corresponding sequent resulting from parsing
     * @throws DafnyParserException
     *             if the sequent was illegally formed. The exception contains a
     *             reference to the erring part of the tree
     */
    public static Sequent parseSequent(@NonNull SymbolTable symbols, @NonNull String string) throws DafnyParserException {
        TermParser tp = new TermParser(symbols);
        return tp.parseSequent(string);
    }

    /**
     * Parses a string to a {@link edu.kit.iti.algover.term.Sequent}.
     *
     * @param string the string to parse
     * @return the corresponding term resulting from parsing
     * @throws DafnyParserException if the term was illegally formed. The exception contains a
     *                              reference to the erring part of the tree
     */
    public Sequent parseSequent(String string) throws DafnyParserException {

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
        DafnyParser.sequent_return result;
        try {
            result = parser.sequent();
        } catch (RecognitionException e) {
            DafnyParserException lex = generateDafnyParserException(parser, e);
            throw lex;
        }

        // pull out the tree and cast it
        DafnyTree t = result.getTree();

        // syntactic desugaring
        SyntacticSugarVistor.visit(t);
        return toSequent(t, new HistoryMap<>(new HashMap<>()));
    }

    /**
     * Generate a DafnyParserException when term parsing fails
     *
     * @param parser DafnyParser
     * @param e      RecognitionException object
     * @return DafynParserException
     */
    private DafnyParserException generateDafnyParserException(DafnyParser parser, RecognitionException e) {
        String msg = parser.getErrorMessage(e, DafnyParser.tokenNames);
        DafnyParserException lex = new DafnyParserException(msg, e);
        lex.setLine(e.line);
        lex.setColumn(e.charPositionInLine);
        if (e.token != null) {
            lex.setLength(e.token.getText().length());
        }
        return lex;
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
            DafnyParserException lex = generateDafnyParserException(parser, e);
            throw lex;
        }

        // pull out the tree and cast it
        DafnyTree t = result.getTree();

        // syntactic desugaring
        SyntacticSugarVistor.visit(t);

        return toTerm(t, new HistoryMap<>(new HashMap<>()));
    }

    /**
     * Create a Sequent form a DafnyTree
     *
     * @param t          DafnyTree representing a sequent
     * @param historyMap
     * @return Sequent object
     * @throws DafnyParserException
     */
    private Sequent toSequent(DafnyTree t, Map<Object, Object> historyMap) throws DafnyParserException {
        DafnyTree antec = t.getChild(0);
        DafnyTree succ = t.getChild(1);
        List<ProofFormula> antecList = translateSemiSequent(antec);
        List<ProofFormula> succList = translateSemiSequent(succ);
        Sequent sequent = new Sequent(antecList, succList);
        return sequent;
    }

    /*
     * translate a parse tree into a Term.
     */
    private Term toTerm(DafnyTree t, Map<String, VariableTerm> boundVariables) throws DafnyParserException {

        try {
            TreeTermTranslator ttt = new TreeTermTranslator(symbols);
            return ttt.build(t);
        } catch (Exception e) {
            DafnyParserException lex = generateDafnyParserException(t, e);
            throw lex;
        }
    }

    private DafnyParserException generateDafnyParserException(DafnyTree antecForm, Exception e) {
        DafnyParserException lex = new DafnyParserException(e);
        lex.setLine(antecForm.getLine());
        lex.setColumn(antecForm.getCharPositionInLine());
        lex.setLength(antecForm.getText().length());
        return lex;
    }

    private Term toTerm(DafnyTree t) throws DafnyParserException {
        return toTerm(t, Collections.emptyMap());
    }

    private List<ProofFormula> translateSemiSequent(DafnyTree semiseq) throws DafnyParserException {
        List<ProofFormula> retList = new ArrayList<>();
        TreeTermTranslator ttt = new TreeTermTranslator(symbols);

        for (DafnyTree antecForm : semiseq.getChildren()) {
            try {
                ProofFormula pf = new ProofFormula(toTerm(antecForm));
                retList.add(pf);
            } catch (Exception e) {
                DafnyParserException lex = generateDafnyParserException(antecForm, e);
                throw lex;
            }
        }
        return retList;
    }
}
