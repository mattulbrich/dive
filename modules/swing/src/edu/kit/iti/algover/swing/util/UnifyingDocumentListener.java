/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 *
 */

package edu.kit.iti.algover.swing.util;

import javax.swing.event.DocumentEvent;
import javax.swing.event.DocumentListener;
import java.util.function.Consumer;

public class UnifyingDocumentListener implements DocumentListener {

    private final Consumer<DocumentEvent> listener;

    public UnifyingDocumentListener(Consumer<DocumentEvent> listener) {
        this.listener = listener;
    }

    @Override
    public void insertUpdate(DocumentEvent e) {
        listener.accept(e);
    }

    @Override
    public void removeUpdate(DocumentEvent e) {
        listener.accept(e);
    }

    @Override
    public void changedUpdate(DocumentEvent e) {
        listener.accept(e);
    }
}
