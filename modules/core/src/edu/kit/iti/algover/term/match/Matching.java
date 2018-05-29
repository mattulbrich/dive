/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 */

package edu.kit.iti.algover.term.match;

import edu.kit.iti.algover.rules.SubtermSelector;
import edu.kit.iti.algover.rules.TermSelector;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.term.builder.TermBuildException;
import edu.kit.iti.algover.util.ImmutableList;
import nonnull.NonNull;
import nonnull.Nullable;

import java.util.Set;

/**
 * Instances of this class are used to describe matching results. Essentially it
 * captures variable assignments.
 *
 * <p>Instances of this class are immutable. Data sharing is performed using
 * {@link ImmutableList}s. All methods modify the entries (the variable
 * assignments) and return a fresh {@link Matching} object.
 *
 * <p>The data is stored in a linear list. If at some point, this is too slow
 * an immutable map (-> TrieMaps) could be implemented or taken (e.g. from
 * guava).
 *
 * @see MatchingEntry
 *
 * @author Mattias Ulbrich
 */
public class Matching {

    /**
     * The empty matching, no assigned variables.
     */
    private static final Matching EMPTY = new Matching(ImmutableList.nil());

    public ImmutableList<MatchingEntry> getEntries() {
        return entries;
    }

    /**
     * the list of variable assignments.
     */
    private final @NonNull ImmutableList<MatchingEntry> entries;

    /**
     * Instantiate a new object.
     *
     * @param entries the entries to use
     */
    private Matching(ImmutableList<MatchingEntry> entries) {
        this.entries = entries;
    }

    /**
     * Retrieve an entry from the entries.
     *
     * @param name name of the schema variable to look up.
     * @return the {@link MatchingEntry} named <code>name</code> or
     * <code>null</code> if no such schema variable exists.
     */
    public @Nullable MatchingEntry get(String name) {
        for (MatchingEntry entry : entries) {
            if(entry.getKey().equals(name)) {
                return entry;
            }
        }
        return null;
    }

    /**
     * Add an entry for a schema variable to the matching.
     *
     * @param name  name of the schema variable to map
     * @param value the term to which the schema term is mapped.
     * @param sel   the term selector which is associated with the entry.
     * @return a fresh Matching object which extends this instance by the entry
     * created from the arguments
     */
    public Matching add(String name, Term value, SubtermSelector sel) {
        MatchingEntry entry = new MatchingEntry(name, value, sel);

        assert get(name) == null;

        return new Matching(entries.append(entry));
    }

    /**
     * Add an entry for an unnamed schema variable to the matching.
     *
     * <p>The first string that matches <code>_<i>X</i></code> and is not in
     * this instance is assigned the value and the selector. This assignment is
     * probably not for public consumption (after all _ is unnamed capture), but
     * for debugging purposes.</p>
     *
     * @param value    the term to which the schema term is mapped.
     * @param selector the term selector which is associated with the entry.
     * @return a fresh Matching object which extends this instance by the entry
     * created from the arguments
     */
    public Matching addUnnamed(Term value, SubtermSelector selector) {
        int no = 0;
        while(get("_" + no) != null) {
            no++;
        }
        return add("_" + no, value, selector);
    }

    /**
     * Add an entry for an unnamed schema variable to the matching.
     *
     * <p>The first string that matches <code>...<i>X</i></code> and is not in
     * this instance is assigned the value and the selector. Mainly for
     * debugging purposes.</p>
     *
     * @param value    the term to which the schema term is mapped.
     * @param selector the term selector which is associated with the entry.
     * @return a fresh Matching object which extends this instance by the entry
     * created from the arguments
     */
    public Matching addEllipsis(Term value, SubtermSelector selector) {
        int no = 0;
        while(get("..." + no) != null) {
            no++;
        }
        return add("..." + no, value, selector);
    }

    /**
     * Use the variable assignment in this instance to instantiate a schematic
     * term
     *
     * @param term the (possibly schematic) term to instantiate
     * @return the term in which the schema variables are instantiated according
     * to this object.
     * @throws TermBuildException if typing of the schema variables does not go
     *                            with the original term.
     */
    public Term instantiate(Term term) throws TermBuildException {
        Term result = term.accept(MatchInstantiator.getInstance(), this);
        if(result == null) {
            return term;
        } else {
            return result;
        }
    }

    /**
     * Returns an empty {@link Matching} object.
     *
     * @return a static reference to an empty matching
     */
    public static Matching emptyMatching() {
        return EMPTY;
    }

    @Override
    public String toString() {
        return entries.toString();
    }


    public void refineContext(TermSelector.SequentPolarity polarity, int no2) {
        this.entries.forEach(matchingEntry -> matchingEntry.refineContext(polarity, no2));

    }
}
