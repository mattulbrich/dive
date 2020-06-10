/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.boogie;

import org.junit.runner.RunWith;
import org.junit.runners.Parameterized.Parameters;

import java.util.List;

@RunWith(ParallelParameterized.class)
public class MultisetTests extends BoogieProcessTest {

    static {
        System.setProperty("edu.kit.iti.algover.keepBPL", "true");
    }

    @Parameters(name = "{1}")
    public static List<Object[]> parameters() throws Exception {
        return parametersFor("multiset/");
    }

}
