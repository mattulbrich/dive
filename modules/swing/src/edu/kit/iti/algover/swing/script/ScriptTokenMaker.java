/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 *
 */

package edu.kit.iti.algover.swing.script;

import edu.kit.iti.algover.parser.DafnyLexer;
import edu.kit.iti.algover.script.ScriptLanguageLexer;
import edu.kit.iti.algover.swing.util.Log;
import org.antlr.runtime.ANTLRStringStream;
import org.antlr.v4.runtime.ANTLRInputStream;
import org.antlr.v4.runtime.CharStreams;
import org.fife.ui.rsyntaxtextarea.Token;
import org.fife.ui.rsyntaxtextarea.TokenMakerBase;

import javax.swing.text.Segment;

import static edu.kit.iti.algover.script.ScriptLanguageLexer.*;

public class ScriptTokenMaker extends TokenMakerBase {

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

        ScriptLanguageLexer lexer = new ScriptLanguageLexer(CharStreams.fromString(text));
        boolean openComment = false;
        try {
            org.antlr.v4.runtime.Token t = lexer.nextToken();
            while(t.getType() != EOF) {
                int pos = t.getCharPositionInLine();
                String txt = t.getText();
                addToken(txt, mapType(t.getType()), startOffset + pos);
                openComment = t.getType() == MULTI_LINE_COMMENT_BEGIN;
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
        case CASES:
        case CASE:
        case MATCH:
            return Token.RESERVED_WORD;


        case MULTI_LINE_COMMENT:
        case MULTI_LINE_COMMENT_BEGIN:
        case SINGLE_LINE_COMMENT:
            return Token.COMMENT_MULTILINE;


        case SEQUENT_LITERAL:
        case TERM_LITERAL:
            return Token.LITERAL_NUMBER_DECIMAL_INT;

        case TRUE:
        case FALSE:
        case STRING_LITERAL:
            return Token.LITERAL_STRING_DOUBLE_QUOTE;

        // return Token.RESERVED_WORD_2;
        // return Token.DATA_TYPE;
        }

        return Token.IDENTIFIER;
    }

}
