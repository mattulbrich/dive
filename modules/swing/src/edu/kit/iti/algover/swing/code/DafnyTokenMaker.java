/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 *
 */

package edu.kit.iti.algover.swing.code;

import edu.kit.iti.algover.parser.DafnyLexer;
import edu.kit.iti.algover.swing.util.Log;
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
    public Token getTokenList(Segment segment, int initialTokenType, int startOffset) {
        resetTokenList();

        String text = segment.toString();

        if(initialTokenType != 0) {
            // ongoing comment
            int end = text.indexOf("*/");
            if(end == -1) {
                addToken(text, Token.COMMENT_MULTILINE, startOffset);
                return firstToken;
            }

            addToken(text.substring(0, end+2), Token.COMMENT_MULTILINE, startOffset);
            text = text.substring(end + 2);
            startOffset += end + 2;
        }

        DafnyLexer lexer = new DafnyLexer(new ANTLRStringStream(text));
        boolean openComment = false;
        try {
            org.antlr.runtime.Token t = lexer.nextToken();
            while(t.getType() != EOF) {
                int pos = t.getCharPositionInLine();
                String txt = t.getText();
                addToken(txt, mapType(t.getType()), startOffset + pos);
                openComment = t.getType() == MULTILINE_COMMENT_BEGIN;
                t = lexer.nextToken();
            }
        } catch (Exception e) {
            if (currentToken == null) {
                addToken(text, Token.ERROR_CHAR, startOffset);
            } else {
                int remainderStart = currentToken.getEndOffset() - startOffset;
                addToken(text.substring(remainderStart), Token.ERROR_CHAR, startOffset + remainderStart);
            }
            Log.stacktrace(Log.VERBOSE, e);
        }

        if(!openComment) {
            addNullToken();
        }

        return firstToken;
    }

    private void addToken(String txt, int type, int offset) {
        addToken(txt.toCharArray(), 0, txt.length() - 1, type, offset);
    }

    private int mapType(int type) {
        switch(type) {
        case DafnyLexer.METHOD:
        case DafnyLexer.CLASS:
        case DafnyLexer.VAR:
        case DafnyLexer.IF:
        case DafnyLexer.IN:
        case DafnyLexer.THEN:
        case DafnyLexer.ELSE:
        case DafnyLexer.RETURNS:
        case DafnyLexer.WHILE:
        case DafnyLexer.FUNCTION:
        case DafnyLexer.ASSIGN:
        case DafnyLexer.RETURN:
        case DafnyLexer.INCLUDE:
        case DafnyLexer.GHOST:
            return Token.RESERVED_WORD;

        case DafnyLexer.REQUIRES:
        case DafnyLexer.ENSURES:
        case DafnyLexer.INVARIANT:
        case DafnyLexer.DECREASES:
        case DafnyLexer.ASSERT:
        case DafnyLexer.ASSUME:
        case DafnyLexer.MODIFIES:
        case DafnyLexer.LEMMA:
        case DafnyLexer.SETTINGS:
        case DafnyLexer.OLD:
        case DafnyLexer.EX:
        case DafnyLexer.ALL:
        case DafnyLexer.LABEL:
            return Token.RESERVED_WORD_2;

        case DafnyLexer.MULTILINE_COMMENT:
        case MULTILINE_COMMENT_BEGIN:
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
