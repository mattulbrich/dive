/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.boogie;

import org.junit.runner.RunWith;
import org.junit.runners.Parameterized.Parameters;

import java.net.MalformedURLException;
import java.util.List;

@RunWith(ParallelParameterized.class)
public class SeqTests extends BoogieProcessTest {

    @Parameters(name = "{1}")
    public static List<Object[]> parameters() throws MalformedURLException {
        return parametersFor("seq/");
    }

}
