/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 *
 */

package edu.kit.iti.algover.swing.code;

import edu.kit.iti.algover.parser.DafnyLexer;
import org.antlr.runtime.ANTLRStringStream;
import org.antlr.runtime.CharStream;
import org.fife.ui.rsyntaxtextarea.AbstractTokenMaker;
import org.fife.ui.rsyntaxtextarea.Token;
import org.fife.ui.rsyntaxtextarea.TokenMakerBase;
import org.fife.ui.rsyntaxtextarea.TokenMap;

import static edu.kit.iti.algover.parser.DafnyLexer.*;
import javax.swing.text.Segment;

public class DafnyTokenMaker extends TokenMakerBase {

    @Override
    public Token getTokenList(Segment text, int initialTokenType, int startOffset) {
        resetTokenList();
        DafnyLexer lexer = new DafnyLexer(new ANTLRStringStream(text.toString() + "\n"));
        try {
            org.antlr.runtime.Token t = lexer.nextToken();
            while(t.getType() != DafnyLexer.EOF) {
                System.out.println("t = " + t);
                int pos = t.getCharPositionInLine();
                String txt = t.getText();
                addToken(txt.toCharArray(), 0, txt.length() - 1, mapType(t.getType()), startOffset + pos);
                t = lexer.nextToken();
            }
            addNullToken();
        } catch (Exception e) {
            int remainderStart = currentToken.textOffset + currentToken.textCount;
            addToken(text, remainderStart, text.count, Token.ERROR_IDENTIFIER, startOffset+remainderStart);
            e.printStackTrace();
        }

       //addToken(text, text.offset, text.count, Token.COMMENT_DOCUMENTATION, startOffset);
       // addNullToken();

        return firstToken;
    }

    private int mapType(int type) {
        switch(type) {
        case DafnyLexer.METHOD:
        case DafnyLexer.CLASS:
        case DafnyLexer.VAR:
        case DafnyLexer.IF:
        case DafnyLexer.THEN:
        case DafnyLexer.ELSE:
        case DafnyLexer.RETURNS:
        case DafnyLexer.WHILE:
        case DafnyLexer.FUNCTION:
        case DafnyLexer.ASSIGN:
        case DafnyLexer.RETURN:
        case DafnyLexer.INCLUDE:
            return Token.RESERVED_WORD;

        case DafnyLexer.REQUIRES:
        case DafnyLexer.ENSURES:
        case DafnyLexer.INVARIANT:
        case DafnyLexer.DECREASES:
        case DafnyLexer.ASSERT:
        case DafnyLexer.MODIFIES:
        case DafnyLexer.LEMMA:
        case DafnyLexer.SETTINGS:
        case DafnyLexer.OLD:
        case DafnyLexer.EX:
        case DafnyLexer.ALL:
        case DafnyLexer.LABEL:
            return Token.RESERVED_WORD_2;

        case DafnyLexer.MULTILINE_COMMENT:
        case DafnyLexer.SINGLELINE_COMMENT:
        case DafnyLexer.ALGOVER_COMMENT:
            return Token.COMMENT_MULTILINE;

        case DafnyLexer.INT:
        case DafnyLexer.BOOL:
        case DafnyLexer.SEQ:
        case DafnyLexer.SET:
        case DafnyLexer.ARRAY:
            return Token.DATA_TYPE;

        case DafnyLexer.INT_LIT:
        case DafnyLexer.TRUE:
        case DafnyLexer.FALSE:
        case DafnyLexer.STRING_LIT:
            return Token.LITERAL_NUMBER_DECIMAL_INT;
        }

        return Token.IDENTIFIER;
    }

}
