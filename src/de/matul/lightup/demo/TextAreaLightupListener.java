/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2016 Karlsruhe Institute of Technology
 */
package de.matul.lightup.demo;

import javax.swing.JTextArea;
import javax.swing.text.BadLocationException;
import javax.swing.text.DefaultHighlighter.DefaultHighlightPainter;

import de.matul.lightup.LightupConnection;
import de.matul.lightup.LightupElement;
import de.matul.lightup.LightupListener;
import de.matul.lightup.Property;

public class TextAreaLightupListener implements LightupListener {

    private static final Property<Object> HIGHLIGHTER_PROP =
            new Property<>("highlighter", Object.class);

    private JTextArea component;

    public TextAreaLightupListener(JTextArea text) {
        this.component = text;
    }

    @Override
    public void showConnection(LightupConnection connection) {
        // is this for me?
        LightupElement receiver = connection.getTo();
        if (receiver instanceof WordLightupElement) {
            WordLightupElement word = (WordLightupElement) receiver;
            String text = component.getText();
            int index = word.getNumber();
            int pos = 0;
            while(index > 0) {
                pos = text.indexOf(' ', pos+1);
                index--;
            }
            int end = text.indexOf(' ', pos+1);

            try {
                Object hl = component.getHighlighter().addHighlight(pos+1, end,
                        new DefaultHighlightPainter(connection.getProperty(LightupConnection.BG_COLOR_PROPERTY)));
                connection.setProperty(HIGHLIGHTER_PROP, hl);
            } catch (BadLocationException e) {
                e.printStackTrace();
            }
        }
    }

    @Override
    public void hideConnection(LightupConnection connection) {
        Object hl = connection.getProperty(HIGHLIGHTER_PROP);
        component.getHighlighter().removeHighlight(hl);
    }

}
