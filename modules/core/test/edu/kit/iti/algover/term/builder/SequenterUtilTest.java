/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 *
 */

package edu.kit.iti.algover.term.builder;

import edu.kit.iti.algover.data.BuiltinSymbols;
import edu.kit.iti.algover.proof.ProofFormula;
import edu.kit.iti.algover.term.parser.TermParser;
import org.junit.Test;

import java.util.Arrays;
import java.util.List;

import static org.junit.Assert.*;

public class SequenterUtilTest {

    @Test
    public void coalesceDuplicates() throws Exception {

        BuiltinSymbols s = new BuiltinSymbols();
        TermBuilder tb = new TermBuilder(s);

        ProofFormula f1 = new ProofFormula(tb.tt(), "L1", "L2");
        ProofFormula f2 = new ProofFormula(tb.tt(), "L1", "L3");
        ProofFormula f3 = new ProofFormula(tb.ff(), "L1", "L2");

        List<ProofFormula> result = SequenterUtil.coalesceDuplicates(Arrays.asList(f1, f2, f2, f3));

        assertEquals("[[L1, L2, L3]: true, [L1, L2]: false]", result.toString());

    }
}