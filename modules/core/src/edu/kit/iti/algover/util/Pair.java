/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2016 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.util;

/**
 * @author Mattias Ulbrich
 */
public class Pair<E, F> {

    public final E fst;
    public final F snd;

    public Pair(E fst, F snd) {
        this.fst = fst;
        this.snd = snd;
    }

    public E getFst() {
        return fst;
    }

    public F getSnd() {
        return snd;
    }

    @Override
    public String toString() {
        return "<" + fst + ", " + snd + ">";
    }

    @Override
    public int hashCode() {
        return (fst == null ? 0 : fst.hashCode()) + 13*(snd == null ? 0 : snd.hashCode());
    }

    @Override
    public boolean equals(Object obj) {
        if (obj instanceof Pair<?,?>) {
            Pair<?,?> p = (Pair<?,?>) obj;
            return (fst == null ? p.fst == null : fst.equals(p.fst)) &&
                   (snd == null ? p.snd == null : snd.equals(p.snd));
        }
        return false;
    }

}
