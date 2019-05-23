/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 *
 */
package edu.kit.iti.algover.swing.actions;

import edu.kit.iti.algover.swing.DiveCenter;

import java.awt.Frame;

import javax.swing.AbstractAction;
import javax.swing.Action;
import javax.swing.Icon;

// TODO Documentation needed
public abstract class BarAction extends AbstractAction {

    private static final long serialVersionUID = -7639080330502488139L;

    public static final String CENTER = "barmanager.center";
    public static final String PARENT_FRAME = "barmanager.parentframe";
    public static final String EDITOR_FRAME = "barmanager.editorframe";

    public BarAction() {
        super();
    }

    public BarAction(String name, Icon icon) {
        super(name, icon);
    }

    public BarAction(String name) {
        super(name);
    }

    protected DiveCenter getDiveCenter() {
        return (DiveCenter) getValue(CENTER);
    }

    protected Frame getParentFrame() {
        return (Frame) getValue(PARENT_FRAME);
    }

    /**
     *
     * @return
     * @see AbstractAction#isSelected(Action)
     */
    protected boolean isSelected() {
        return Boolean.TRUE.equals(getValue(Action.SELECTED_KEY));
    }

    protected void setSelected(boolean selected) {
        putValue(Action.SELECTED_KEY, selected);
    }

    protected void setIcon(Icon icon) {
        putValue(SMALL_ICON, icon);
    }

}
