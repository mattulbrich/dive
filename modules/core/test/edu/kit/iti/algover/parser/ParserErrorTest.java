/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 *
 */

package edu.kit.iti.algover.parser;

import edu.kit.iti.algover.util.TestUtil;
import org.junit.Ignore;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.ExpectedException;

import java.io.ByteArrayInputStream;
import java.io.IOException;

// does not only test parser, but also semantic analysis
public class ParserErrorTest {

    @Rule
    public ExpectedException thrown = ExpectedException.none();

    // from an exception
    @Test
    public void unknownFunction() throws Exception {
        thrown.expect(DafnyException.class);
        thrown.expectMessage("Unknown method or function: unknownFunction");
        parse("method m() ensures unknownFunction() == 0 {}");
    }

    // from an exception
    @Test @Ignore
    public void illegalAccess() throws Exception {
        thrown.expect(DafnyException.class);
        thrown.expectMessage("");
        parse("method m(i:int) { i[0] := 0; }");
    }


    private void parse(String program) throws Exception {
        TestUtil.mockProject(program);
    }

}
