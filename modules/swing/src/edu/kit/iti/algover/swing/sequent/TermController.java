/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 *
 */

package edu.kit.iti.algover.swing.sequent;

import edu.kit.iti.algover.proof.ProofFormula;
import edu.kit.iti.algover.rules.SubtermSelector;
import edu.kit.iti.algover.rules.TermSelector;
import edu.kit.iti.algover.swing.DiveCenter;
import edu.kit.iti.algover.swing.util.GUIUtil;
import edu.kit.iti.algover.swing.util.Log;
import edu.kit.iti.algover.swing.util.NotScrollingCaret;
import edu.kit.iti.algover.swing.util.Settings;
import edu.kit.iti.algover.swing.util.Signal;
import edu.kit.iti.algover.term.prettyprint.AnnotatedString;
import edu.kit.iti.algover.term.prettyprint.AnnotatedString.Style;
import edu.kit.iti.algover.term.prettyprint.AnnotatedString.TermElement;
import edu.kit.iti.algover.term.prettyprint.PrettyPrint;
import edu.kit.iti.algover.util.ImmutableList;
import edu.kit.iti.algover.util.Immutables;
import edu.kit.iti.algover.util.Util;

import javax.swing.*;
import javax.swing.border.Border;
import javax.swing.text.AttributeSet;
import javax.swing.text.BadLocationException;
import javax.swing.text.DefaultHighlighter;
import javax.swing.text.DefaultHighlighter.DefaultHighlightPainter;
import javax.swing.text.MutableAttributeSet;
import javax.swing.text.SimpleAttributeSet;
import javax.swing.text.StyleConstants;
import java.awt.*;
import java.awt.event.ComponentAdapter;
import java.awt.event.ComponentEvent;
import java.awt.event.MouseAdapter;
import java.awt.event.MouseEvent;
import java.util.Set;


/**
 * This class manages an individual text field that displays a single formula.
 *
 * @author Mattias Ulbrich
 */
@SuppressWarnings("checkstyle:JavadocVariable")
public class TermController extends MouseAdapter {

    @SuppressWarnings("checkstyle:StaticVariableName")
    private static Settings S = Settings.getInstance();

    /*
     * some UI constants
     */
    private static final Font FONT = S.getFont("dive.termcomponent.font", null);

    // the highlight color should be bright
    private static final Color HIGHLIGHT_COLOR =
            S.getColor("dive.termcomponent.highlightcolor", Color.ORANGE);

    private static final Color SELECTION_COLOR =
            S.getColor("dive.termcomponent.selectioncolor", Color.YELLOW);

    // border color needs to match background of sequent view
    private static final Color BORDER_COLOR =
            S.getColor("dive.termcomponent.bordercolor", Color.DARK_GRAY);

    // variables should be noticed
    private static final Color VARIABLE_FOREGROUND =
            S.getColor("dive.termcomponent.variableforeground", Color.CYAN.darker());

    // variables should be noticed
    private static final Color USER_ENTITY_FOREGROUND =
            S.getColor("dive.termcomponent.userentityforeground", Color.GREEN.darker());

    // keywords should be painted less noticeable
    private static final Color KEYWORD_FOREGROUND =
            S.getColor("dive.termcomponent.keywordforeground", Color.MAGENTA.darker());

    // types should be painted less noticeable
    private static final Color TYPE_FOREGROUND =
            S.getColor("dive.termcomponent.typeforeground", Color.LIGHT_GRAY);

    // marking for an assumption
    private static final Color LIGHT_MARKING_COLOR =
            S.getColor("dive.termcomponent.assumptionforeground", new Color(0xd0d0ff));

    // marking for a find clause
    private static final Color DARK_MARKING_COLOR =
            S.getColor("dive.termcomponent.findforeground", new Color(0xb0b0ff));

    // empty border
    private static final Border BORDER =
            BorderFactory.createCompoundBorder(
                BorderFactory.createCompoundBorder(
                        new TagBorder(), BorderFactory.createLineBorder(BORDER_COLOR)
                    ),
                BorderFactory.createEmptyBorder(5, 5, 5, 5));


    /*
     * This is used by AnnotatedStringWithStyles to construct styles.
     */
    private final AnnotatedString.AttributeSetFactory attributeFactory =
            new AnnotatedString.AttributeSetFactory() {
                @Override
                public AttributeSet makeStyle(Set<Style> styles) {


                    MutableAttributeSet retval = new SimpleAttributeSet();

                    for (Style style : styles) {
                        switch(style) {
                        case KEYWORD:
                            StyleConstants.setForeground(retval, KEYWORD_FOREGROUND);
                            break;
                        case VARIABLE:
                            StyleConstants.setForeground(retval, VARIABLE_FOREGROUND);
                            break;
                        case TYPE:
                            StyleConstants.setForeground(retval, TYPE_FOREGROUND);
                            break;
                        case USER_ENTITY:
                            StyleConstants.setForeground(retval, USER_ENTITY_FOREGROUND);
                            break;
                        case CLOSED:
                            StyleConstants.setItalic(retval, true);
                            break;
                        }
                    }

                    return retval;
                }

            };

    private final JTextPane component;
    private final PrettyPrint prettyPrinter;
    private final Object mouseHighlight;
    private final Object selectionHighlight;
    private DiveCenter diveCenter;
    private ProofFormula proofFormula;
    private TermSelector termSelector;
    private int lineWidth;
    private AnnotatedString annotatedString;
    private SubtermSelector mouseSelection;
    private ImmutableList<TermSelector> replacementHighlights = ImmutableList.nil();

    @SuppressWarnings("checkstyle:JavadocMethod")
    public TermController(DiveCenter diveCenter, ProofFormula proofFormula, TermSelector termSelector) {
        this.diveCenter = diveCenter;
        this.proofFormula = proofFormula;
        this.termSelector = termSelector;

        this.component = new JTextPane();

        component.setEditable(false);
        component.setFocusable(false);
        component.setBorder(BORDER);
        component.setFont(FONT);
        component.setCaret(new NotScrollingCaret());
        component.addMouseListener(this);
        component.addMouseMotionListener(this);
        DefaultHighlighter highlight = new DefaultHighlighter();
        component.setHighlighter(highlight);
        component.putClientProperty("indented", true);
        component.addComponentListener(new ComponentAdapter() {
            @Override
            public void componentResized(ComponentEvent e) {
                reprint();
            }
        });
        component.putClientProperty(TagBorder.TAG_KEY,
                Util.commatize(proofFormula.getLabels()));

        try {
            this.mouseHighlight = component.getHighlighter().addHighlight(0, 0,
                    new DefaultHighlightPainter(HIGHLIGHT_COLOR));
            this.selectionHighlight = component.getHighlighter().addHighlight(0, 0,
                    new DefaultHighlightPainter(SELECTION_COLOR));
        } catch (BadLocationException ex) {
            // Must always work!
            Log.log(Log.WARNING, "Unexpected bad location error");
            Log.stacktrace(Log.WARNING, ex);
            throw new Error(ex);
        }

        this.prettyPrinter = new PrettyPrint();
        reprint();
    }

    /**
     * React to a changed termselector.
     *
     * Update my highlight accordingly.
     *
     * This is not done by subscribing to a property because unsubscribing
     * would be necessary.
     *
     * @param ts the new termselector
     */
    public void updateTermSelector(TermSelector ts) {
        try {
            if (ts == null || !ts.getToplevelSelector().equals(this.termSelector)) {
                component.getHighlighter().changeHighlight(selectionHighlight, 0, 0);
            } else if (ts.isToplevel()) {
                component.getHighlighter().changeHighlight(selectionHighlight, 0, annotatedString.length());
            } else {
                for (TermElement element : annotatedString.getAllTermElements()) {
                    if (element.getSubtermSelector().equals(ts.getSubtermSelector())) {
                        int begin = element.getBegin();
                        int end = element.getEnd();
                        component.getHighlighter().changeHighlight(selectionHighlight, begin, end);
                        break;
                    }
                }
            }
        } catch (BadLocationException ex) {
            // Must always work!
            Log.log(Log.WARNING, "Unexpected bad location error");
            Log.stacktrace(Log.WARNING, ex);
            throw new Error(ex);
        }
    }

    public void setReplacementHighlights(ImmutableList<TermSelector> selectors) {
        this.replacementHighlights = selectors.filter(ts -> ts.getToplevelSelector().equals(this.termSelector));
    }

    private void paintReplacementHighlights() {
        try {
            for (TermSelector ts : replacementHighlights) {
                if (ts.isToplevel()) {
                    component.getHighlighter().addHighlight(0, annotatedString.length(),
                            new DefaultHighlightPainter(DARK_MARKING_COLOR));
                } else {
                    for (TermElement element : annotatedString.getAllTermElements()) {
                        if (element.getSubtermSelector().equals(ts.getSubtermSelector())) {
                            int begin = element.getBegin();
                            int end = element.getEnd();
                            component.getHighlighter().addHighlight(begin, end,
                                    new DefaultHighlightPainter(DARK_MARKING_COLOR));
                            break;
                        }
                    }
                }
            }
        } catch (BadLocationException ex) {
            // Must always work!
            Log.log(Log.WARNING, "Unexpected bad location error");
            Log.stacktrace(Log.WARNING, ex);
            throw new Error(ex);
        }
    }


    /**
     * React to the sources being unavailable.
     *
     * This is not done by subscribing to a property because unsubscribing
     * would be necessary.
     *
     * @param modified flag to show if active/deactivated
     */
    public void sourcesModified(boolean modified) {
        if (modified) {
            component.setEnabled(false);
            mouseExited(null);
        } else {
            component.setEnabled(true);
        }
    }

    private void reprint() {
        int newLineWidth = computeLineWidth();
        if (newLineWidth != lineWidth) {
            this.annotatedString = prettyPrinter.print(proofFormula.getTerm(), newLineWidth);
            component.setText("");
            annotatedString.appendToDocument(component.getDocument(), attributeFactory);
            lineWidth = newLineWidth;
            updateTermSelector(diveCenter.properties().termSelector.getValue());
            paintReplacementHighlights();
        }
    }

    /**
     * Return the Component that this controller handles
     *
     * @return the text pane, not null
     */
    public Component getComponent() {
        return component;
    }


    /**
     * Computes the line width.
     *
     * Uses the dimensions and fontmetrics. Needs a proportional font.
     * (taken from KeY!)
     *
     * @return the number of characters in one line
     */
    private int computeLineWidth() {
        // assumes we have a uniform font width
        int maxChars = component.getSize().width /
                component.getFontMetrics(component.getFont()).charWidth('i');

        if (maxChars > 1) {
            maxChars -= 1;
        }

        return maxChars;
    }

    // -----------
    // MOUSE
    // -----------

    /*
     * Mouse exited the component: remove highlighting
     */
    @Override
    public void mouseExited(MouseEvent e) {
        try {
            component.getHighlighter().changeHighlight(mouseHighlight, 0, 0);
            mouseSelection = null;
        } catch (BadLocationException ex) {
            Log.log(Log.WARNING, "Unexpected bad location error");
            Log.stacktrace(Log.WARNING, ex);
        }
    }

    /*
     * Mouse moved: move the highlighting
     */
    @Override
    public void mouseMoved(MouseEvent e) {
        if(!component.isEnabled()) {
            return;
        }

        Point p = e.getPoint();
        Log.enter(p);
        int index = viewToModel(p);
        try {
            if (index >= 0 && index < annotatedString.length()) {
                TermElement element = annotatedString.getTermElementAt(index);
                int begin = element.getBegin();
                int end = element.getEnd();
                component.getHighlighter().changeHighlight(mouseHighlight, begin, end);

                mouseSelection = annotatedString.getTermElementAt(index).getSubtermSelector();

                if (null != mouseSelection) {
                    Log.log(Log.VERBOSE, mouseSelection);
                }
            } else {
                component.getHighlighter().changeHighlight(mouseHighlight, 0, 0);
                mouseSelection = null;
            }
        } catch (BadLocationException ex) {
            ex.printStackTrace();
        }
    }

    @Override
    public void mouseClicked(MouseEvent e) {

        if (e.getClickCount() == 1) {
            if (SwingUtilities.isRightMouseButton(e)) {
                showPopup(e);
            } else if (SwingUtilities.isLeftMouseButton(e)) {
                selectTerm(e);
            }
        }
        // TODO Double click
    }

    private void showPopup(MouseEvent e) {
        Point p = e.getPoint();
        Log.enter(p);
        int index = viewToModel(p);
        TermSelector selector;
        String text;
        if (index >= 0 && index < annotatedString.length()) {
            TermElement element = annotatedString.getTermElementAt(index);
            selector = new TermSelector(termSelector, element.getSubtermSelector());
            text = annotatedString.toString().substring(element.getBegin(), element.getEnd());
        } else {
            selector = termSelector;
            text = annotatedString.toString();
        }

        Signal<String> insert = diveCenter.properties().insertIntoScriptCaret;

        JPopupMenu popup = new JPopupMenu();
        popup.add(mkPopupItem("Copy full term",
                () -> GUIUtil.copyToClipboard(text)));
        popup.add(mkPopupItem("Copy unique term",
                () -> GUIUtil.copyToClipboard(text)));
        popup.add(mkPopupItem("Copy term selector",
                () -> GUIUtil.copyToClipboard(selector.toString())));
        popup.add(new JSeparator());
        popup.add(mkPopupItem("Insert full term",
                () -> insert.fire(text)));
        popup.add(mkPopupItem("Insert unique term",
                () -> insert.fire(text)));
        popup.add(mkPopupItem("Insert term selector",
                () -> insert.fire(selector.toString())));
        popup.show(component, e.getX(), e.getY());
    }

    private JMenuItem mkPopupItem(String title, Runnable action) {
        JMenuItem menuItem = new JMenuItem(title);
        menuItem.addActionListener(e -> action.run());
        return menuItem;
    }

    private void selectTerm(MouseEvent e) {
        Point p = e.getPoint();
        Log.enter(p);
        int index = viewToModel(p);
        if (index >= 0 && index < annotatedString.length()) {
            TermElement element = annotatedString.getTermElementAt(index);
            diveCenter.properties().termSelector.setValue(new TermSelector(termSelector, element.getSubtermSelector()));
        }
    }

    // stolen from KeY
    private int viewToModel(Point p) {
        String seqText = component.getText();

        // bugfix for empty strings
        if (seqText.length() == 0) {
            return 0;
        }

        int cursorPosition = component.viewToModel(p);

        cursorPosition -= (cursorPosition > 0 ? 1 : 0);

        cursorPosition = (cursorPosition >= seqText.length() ? seqText.length() - 1
                : cursorPosition);
        cursorPosition = (cursorPosition >= 0 ? cursorPosition : 0);

        int previousCharacterWidth = component.getFontMetrics(component.getFont()).charWidth(
                seqText.charAt(cursorPosition));

        int characterIndex = component.viewToModel(new Point((int) p.getX()
                - (previousCharacterWidth / 2), (int) p.getY()));

        characterIndex = Math.max(0, characterIndex);

        return characterIndex;
    }

}


