/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2016 Karlsruhe Institute of Technology
 */
package de.matul.lightup;

import java.awt.Color;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

public class LightupManager {

    private List<LightupListener> listeners = new ArrayList<>();

    private Map<Integer, LightupConnection> activeConnections = new HashMap<>();

    public void addLightupListener(LightupListener listener) {
        if(!listeners.contains(listener)) {
            listeners.add(listener);
        }
    }

    public void removeLightupListener(LightupListener listener) {
        listeners.remove(listener);
    }

    public void showConnection(LightupConnection connection) {
        activeConnections.put(connection.getId(), connection);

        for (LightupListener listener : listeners) {
            listener.showConnection(connection);
        }
    }

    public void hideConnection(LightupConnection connection) {

        if(activeConnections.get(connection.getId()) == null) {
            throw new IllegalArgumentException("Connection is no longer maintained!");
        }

        activeConnections.remove(connection.getId());

        for (LightupListener listener : listeners) {
            listener.hideConnection(connection);
        }
    }

}
