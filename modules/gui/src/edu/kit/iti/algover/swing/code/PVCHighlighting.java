/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 *
 */

package edu.kit.iti.algover.swing.code;

import edu.kit.iti.algover.parser.DafnyTree;
import edu.kit.iti.algover.swing.util.GUIUtil;
import edu.kit.iti.algover.swing.util.Log;
import edu.kit.iti.algover.swing.util.Settings;
import edu.kit.iti.algover.symbex.AssertionElement;
import edu.kit.iti.algover.symbex.PathConditionElement;
import edu.kit.iti.algover.symbex.PathConditionElement.AssumptionType;
import edu.kit.iti.algover.symbex.SymbexPath;
import org.antlr.runtime.Token;
import org.fife.ui.rsyntaxtextarea.RSyntaxTextArea;

import javax.swing.text.BadLocationException;
import javax.swing.text.DefaultHighlighter.DefaultHighlightPainter;
import javax.swing.text.Highlighter.HighlightPainter;
import java.awt.*;
import java.util.List;

public class PVCHighlighting {

    public static final Settings S = Settings.getInstance();

    public static final Color ASSIGNMENT_COLOR =
            S.getColor("dive.symbexcolor.assignment", Color.CYAN);
    private static final HighlightPainter ASSIGNMENT_HIGHLIGHT =
            new DefaultHighlightPainter(ASSIGNMENT_COLOR);

    public static final Color PATH_CONDITION_COLOR =
            S.getColor("dive.symbexcolor.condition", Color.green.brighter());
    private static final HighlightPainter POSITIVE_GUARD_HIGHLIGHT =
            new BarHighlightPainter(PATH_CONDITION_COLOR, 4, .9d);
    private static final HighlightPainter NEGATIVE_GUARD_HIGHLIGHT =
            new BarHighlightPainter(PATH_CONDITION_COLOR, 4, .5d);
    private static final HighlightPainter OTHER_PATH_CONDITION =
            new DefaultHighlightPainter(PATH_CONDITION_COLOR);

    public static final Color ASSERTION_COLOR =
            S.getColor("dive.symbexcolor.assertion", Color.red.brighter());
    private static final HighlightPainter ASSERTTION_HIGHLIGHT =
            new DefaultHighlightPainter(ASSERTION_COLOR);


    public static void updateHighlight(SymbexPath symbexPath, RSyntaxTextArea textArea) {
        try {

            HighlightPainter painter = ASSIGNMENT_HIGHLIGHT;
            for (DafnyTree tree : symbexPath.getAssignmentHistory()) {
                addHighlight(textArea, tree, painter);
            }

            for (PathConditionElement pathCondition : symbexPath.getPathConditions()) {
                HighlightPainter color;
                if (isPositiveGuard(pathCondition)) {
                    color = POSITIVE_GUARD_HIGHLIGHT;
                } else if (isNegativeGuard(pathCondition)) {
                    color = NEGATIVE_GUARD_HIGHLIGHT;
                } else {
                    color = OTHER_PATH_CONDITION;
                }
                addHighlight(textArea, pathCondition.getExpression(), color);
            }

            for (AssertionElement obl : symbexPath.getProofObligations()) {
                addHighlight(textArea, obl.getOrigin(), ASSERTTION_HIGHLIGHT);
            }

        } catch (BadLocationException ex) {
            Log.log(Log.DEBUG, "Wrong index calculation for highlights of symb. execution");
            Log.stacktrace(Log.DEBUG, ex);
        }
    }

    private static boolean isNegativeGuard(PathConditionElement pathConditionElement) {
        return pathConditionElement.getType() == AssumptionType.IF_ELSE
                || pathConditionElement.getType() == AssumptionType.WHILE_FALSE;
    }

    private static boolean isPositiveGuard(PathConditionElement pathConditionElement) {
        return pathConditionElement.getType() == AssumptionType.IF_THEN
                || pathConditionElement.getType() == AssumptionType.WHILE_TRUE;
    }

    private static Object addHighlight(RSyntaxTextArea textArea, DafnyTree tree, HighlightPainter painter) throws BadLocationException {
        Token fromToken = tree.getStartToken();
        Token stopToken = tree.getStopToken();
        return addHighlight(textArea, fromToken, stopToken, painter);
    }

    private static Object addHighlight(RSyntaxTextArea textArea, Token fromToken, Token stopToken, HighlightPainter painter) throws BadLocationException {
        int fromLine = fromToken.getLine();
        int fromCol = fromToken.getCharPositionInLine() + 1;
        int fromPos = GUIUtil.linecolToPos(textArea.getText(), fromLine, fromCol);
        int toLine = stopToken.getLine();
        int toCol = stopToken.getCharPositionInLine() + 1;
        String text = stopToken.getText();
        int toPos = GUIUtil.linecolToPos(textArea.getText(), toLine, toCol)
                + (text == null ? 0 : text.length());

        System.out.println("fromPos = " + fromPos);
        System.out.println("toPos = " + toPos);
        System.out.println("textArea = " + textArea.getText().length());
        if (fromPos < 0 || toPos < 0) {
            return null;
        }
        return textArea.getHighlighter().addHighlight(fromPos, toPos, painter);
    }


}
