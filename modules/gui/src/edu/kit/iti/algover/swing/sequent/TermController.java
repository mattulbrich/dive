/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 *  
 */

package edu.kit.iti.algover.swing.sequent;

import edu.kit.iti.algover.proof.ProofFormula;
import edu.kit.iti.algover.rules.TermSelector;
import edu.kit.iti.algover.swing.DiveCenter;
import edu.kit.iti.algover.swing.util.NotScrollingCaret;
import edu.kit.iti.algover.swing.util.Settings;
import edu.kit.iti.algover.term.prettyprint.AnnotatedString;
import edu.kit.iti.algover.term.prettyprint.AnnotatedString.Style;
import edu.kit.iti.algover.term.prettyprint.PrettyPrint;

import javax.swing.*;
import javax.swing.border.Border;
import javax.swing.text.AttributeSet;
import javax.swing.text.MutableAttributeSet;
import javax.swing.text.SimpleAttributeSet;
import javax.swing.text.StyleConstants;
import java.awt.*;
import java.util.Set;

public class TermController {

    private static Settings S = Settings.getInstance();

    /**
     * some UI constants
     */
    private static final Font FONT = S.getFont("dive.termcomponent.font", null);

    // the highlight color should be bright
    private static final Color HIGHLIGHT_COLOR =
            S.getColor("dive.termcomponent.highlightcolor", Color.ORANGE);

    // border color needs to match background of sequent view
    private static final Color BORDER_COLOR =
            S.getColor("dive.termcomponent.bordercolor", Color.DARK_GRAY);

    // variables should be noticed
    private static final Color VARIABLE_FOREGROUND =
            S.getColor("dive.termcomponent.variableforeground", Color.MAGENTA);

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
            S.getColor("dive.termcomponent.assumptionforeground", Color.LIGHT_GRAY);

    // marking for a find clause
    private static final Color DARK_MARKING_COLOR =
            S.getColor("dive.termcomponent.findforeground", Color.LIGHT_GRAY);

    // empty border
    private static final Border BORDER = BorderFactory.createCompoundBorder(
            BorderFactory.createLineBorder(BORDER_COLOR), BorderFactory
                    .createEmptyBorder(5, 5, 5, 5));


    /*
     * This is used by AnnotatedStringWithStyles to construct styles.
     */
    private final AnnotatedString.AttributeSetFactory attributeFactory =
            new AnnotatedString.AttributeSetFactory() {
                @Override
                public AttributeSet makeStyle(Set<Style> styles) {


                    MutableAttributeSet retval = new SimpleAttributeSet();
                    if(FONT != null) {
                        StyleConstants.setFontFamily(retval, FONT.getFamily());
                        StyleConstants.setFontSize(retval, FONT.getSize());
                    }

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
    private DiveCenter diveCenter;
    private ProofFormula proofFormula;
    private TermSelector termSelector;

    public TermController(DiveCenter diveCenter, ProofFormula proofFormula, TermSelector termSelector) {
        this.diveCenter = diveCenter;
        this.proofFormula = proofFormula;
        this.termSelector = termSelector;

        this.component = new JTextPane();

        component.setEditable(false);
        component.setFocusable(false);
        component.setBorder(BORDER);
        component.setCaret(new NotScrollingCaret());

        PrettyPrint pp = new PrettyPrint();
        AnnotatedString annotatedString = pp.print(proofFormula.getTerm());
        annotatedString.appendToDocument(component.getDocument(), attributeFactory);
    }

    public Component getComponent() {
        return component;
    }
}


