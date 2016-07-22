/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2016 Karlsruhe Institute of Technology
 */
package de.matul.lightup.demo;

import de.matul.lightup.LightupElement;

public class WordLightupElement implements LightupElement {

    private String string;
    private int number;

    public WordLightupElement(String string, int i) {
        this.string = string;
        this.number = i;
    }

    @Override
    public String toString() {
        return string;
    }

    public int getNumber() {
        return number;
    }
}
