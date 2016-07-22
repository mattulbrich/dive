/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2016 Karlsruhe Institute of Technology
 */
package de.matul.lightup.demo;

import javax.swing.JList;

import de.matul.lightup.LightupConnection;
import de.matul.lightup.LightupElement;
import de.matul.lightup.LightupListener;

public class ListLightupListener implements LightupListener {

    private JList<WordLightupElement> list;
    private LightupConnection[] connections;

    public ListLightupListener(JList<WordLightupElement> list, LightupConnection[] connections) {
        this.list = list;
        this.connections = connections;
    }

    @Override
    public void showConnection(LightupConnection connection) {
        LightupElement receiver = connection.getTo();
        if (receiver instanceof WordLightupElement) {
            WordLightupElement wle = (WordLightupElement) receiver;
            int i = wle.getNumber();
            connections[i] = connection;
            list.repaint();
        }
    }

    @Override
    public void hideConnection(LightupConnection connection) {
        LightupElement receiver = connection.getTo();
        if (receiver instanceof WordLightupElement) {
            WordLightupElement wle = (WordLightupElement) receiver;
            int i = wle.getNumber();
            connections[i] = null;
            list.repaint();
        }
    }

    public LightupConnection getConnection(int number) {
        return connections[number];
    }

}
