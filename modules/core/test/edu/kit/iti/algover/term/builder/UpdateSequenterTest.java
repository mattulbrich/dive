/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.term.builder;

public class UpdateSequenterTest extends SequenterTest {

    protected String expectedSuccedent(String string) {
        return "[(let local := p :: (let r := local :: $gt(r, 0)))]";
    }

    protected String expectedAntecedent(String string) {
        return "[$gt(p, 0), (let local := p :: $gt(local, 0))]";
    }

    @Override
    protected PVCSequenter makeSequenter() {
        return new UpdateSequenter();
    }
}
