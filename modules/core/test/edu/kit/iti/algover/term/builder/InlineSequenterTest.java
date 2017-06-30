/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.term.builder;

public class InlineSequenterTest extends SequenterTest {

    protected String expectedSuccedent(String string) {
        return "[$gt(p, 0)]";
    }

    protected String expectedAntecedent(String string) {
        return "[$gt(p, 0), $gt(p, 0)]";
    }

    @Override
    protected PVCSequenter makeSequenter() {
        return new InlineSequenter();
    }
}
