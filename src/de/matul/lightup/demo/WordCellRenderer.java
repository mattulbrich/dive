/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2016 Karlsruhe Institute of Technology
 */
package de.matul.lightup.demo;

import java.awt.Component;

import javax.swing.BorderFactory;
import javax.swing.JLabel;
import javax.swing.JList;
import javax.swing.ListCellRenderer;
import javax.swing.border.Border;
import javax.swing.border.EmptyBorder;

import de.matul.lightup.LightupConnection;
import de.matul.lightup.LightupManager;

public class WordCellRenderer extends JLabel implements ListCellRenderer<WordLightupElement> {

    private LightupManager lightupManager;
    private LightupConnection[] connectionsPerWord;

    public WordCellRenderer(LightupManager lightupManager, LightupConnection[] connectionsPerWord) {
        this.lightupManager = lightupManager;
        this.connectionsPerWord = connectionsPerWord;
        setOpaque(true);
        setName("List.cellRenderer");
    }

    @Override
    public Component getListCellRendererComponent(
            JList<? extends WordLightupElement> list, WordLightupElement value,
            int index, boolean isSelected, boolean cellHasFocus) {

        LightupConnection conn = connectionsPerWord[value.getNumber()];

        setComponentOrientation(list.getComponentOrientation());

        setBorder(new EmptyBorder(5, 5, 5, 5));
        if(conn != null) {
            Border bevel = BorderFactory.createLineBorder(conn.getColor(), 2);
            setBorder(BorderFactory.createCompoundBorder(bevel, getBorder()));
        }

        if (isSelected) {
            setBackground(list.getSelectionBackground());
            setForeground(list.getSelectionForeground());
        } else {
            setForeground(list.getForeground());
            if(conn != null) {
                setBackground(conn.getProperty(LightupConnection.BG_COLOR_PROPERTY));
            } else {
                setBackground(list.getBackground());
            }
        }

        setEnabled(list.isEnabled());
        setFont(list.getFont());

        setText(value.toString());

        return this;
    }

}
