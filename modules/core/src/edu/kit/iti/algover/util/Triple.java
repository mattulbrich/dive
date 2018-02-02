/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.util;

import java.util.Objects;

import edu.kit.iti.algover.rules.SubtermSelector;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.term.match.Matching;

/**
 * @author Mattias Ulbrich
 */
public class Triple<E, F, G> {

    public final E fst;
    public final F snd;
    public final G trd;

    public Triple(E fst, F snd, G trd) {
        this.fst = fst;
        this.snd = snd;
        this.trd = trd;
    }

    public E getFst() {
        return fst;
    }

    public F getSnd() {
        return snd;
    }

    public G getTrd() {
        return trd;
    }

    @Override
    public String toString() {
        return "<" + fst + ", " + snd + "," + trd + ">";
    }

    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + ((fst == null) ? 0 : fst.hashCode());
        result = prime * result + ((snd == null) ? 0 : snd.hashCode());
        result = prime * result + ((trd == null) ? 0 : trd.hashCode());
        return result;
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj) {
            return true;
        }
        if (obj == null) {
            return false;
        }
        if (getClass() != obj.getClass()) {
            return false;
        }
        Triple<?,?,?> other = (Triple<?,?,?>) obj;

        return Objects.equals(fst, other.fst) &&
                Objects.equals(snd, other.snd) &&
                Objects.equals(trd, other.trd);

    }

}
