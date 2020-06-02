/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 *
 */
/*
 * This file is part of
 *    ivil - Interactive Verification on Intermediate Language
 *
 * Copyright (C) 2009-2012 Karlsruhe Institute of Technology
 *
 * The system is protected by the GNU General Public License.
 * See LICENSE.TXT (distributed with this file) for details.
 */
package edu.kit.iti.algover.swing.util;

import java.util.Collection;
import java.util.Collections;
import java.util.LinkedList;
import java.util.List;
import java.util.logging.Level;
import java.util.logging.Logger;
import java.util.prefs.BackingStoreException;
import java.util.prefs.Preferences;

import nonnull.DeepNonNull;
import nonnull.NonNull;

/**
 * This class is a small helper class to implement persistent input history
 * storage.
 *
 * The history is read and stored as entries into the {@link Preferences}
 * system.
 *
 * Several input histories can exist at the same time if they use different
 * identifiers.
 */
public class InputHistory {

    private static final Logger logger =
            Logger.getLogger(InputHistory.class.getName());

    /**
     * The name under which the preferences are stored for this object.
     */
    private final String identifier;

    /**
     * The maximum number of entires in this object. The list is trimmed to this
     * if necessary.
     */
    private final int size;

    /**
     * The actual list of entries.
     *
     * This is <code>null</code> in the beginning and only incarnated on demand.
     */
    private LinkedList<String> historyList;


    /**
     * Instantiates a new input history.
     *
     * @param identifier
     *            the identifier under which the persistent storage is accessed
     * @param size
     *            the positive size of this list
     */
    public InputHistory(@NonNull String identifier, int size) {
        this.identifier = identifier;
        this.size = size;
    }

    /**
     * Gets the history of entries for this object.
     *
     * @return an immutable view to the entries in the history
     */
    public @NonNull List<String> getHistory() {
        if (historyList == null) {
            readHistoryList();
        }
        return Collections.unmodifiableList(historyList);
    }

    /*
     * read the list from the preferences.
     */
    private synchronized void readHistoryList() {
        // may be the case due to concurrency
        if (historyList != null) {
            return;
        }

        historyList = new LinkedList<String>();

        Preferences pref = Preferences.userNodeForPackage(InputHistory.class);
        for (int i = 0; i < size; i++) {
            String entry = pref.get(identifier + "." + i, null);
            if (entry == null) {
                break;
            }
            historyList.add(entry);
        }
    }


    /**
     * Adds an entry to the history list.
     *
     * If the string is already present in the list, it is moved to the front.
     * Otherwise it is added to the front
     *
     * The list is trimmed to the given size if necessary, possibly throwing
     * away one old entry.
     *
     * @param entry
     *            the input entry to be added to the history list
     */
    public synchronized void add(@NonNull String entry) {
        if (historyList == null) {
            readHistoryList();
        }
        historyList.remove(entry);
        historyList.addFirst(entry);
        if(historyList.size() > size) {
            historyList.removeLast();
        }
    }

    /**
     * Adds a collection of entries to the history list.
     *
     * Strings already present in the list are moved to the front. Otherwise
     * they are added to the front
     *
     * The list is trimmed to the given size if necessary, possibly throwing
     * away one or more old entries.
     *
     * @param entries
     *            the input entries to be added to the history list
     */
    public synchronized void addAll(@DeepNonNull Collection<String> entries) {
        if (historyList == null) {
            readHistoryList();
        }
        historyList.removeAll(entries);
        historyList.addAll(0, entries);
        while(historyList.size() > size) {
            historyList.removeLast();
        }
    }

    public void saveToPreferences() {
        if (historyList == null) {
            return;
        }

        Preferences pref = Preferences.userNodeForPackage(InputHistory.class);
        int cnt = 0;
        for (String entry : historyList) {
            pref.put(identifier + "." + cnt, entry);
            cnt ++;
        }
        try {
            pref.flush();
        } catch (BackingStoreException e) {
            logger.log(Level.WARNING, "Error while synchronising preferences", e);
        }
    }

}
