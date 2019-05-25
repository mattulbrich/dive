/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 *
 */
package edu.kit.iti.algover.project;

import edu.kit.iti.algover.data.BuiltinSymbols;
import edu.kit.iti.algover.data.MapSymbolTable;
import edu.kit.iti.algover.data.SymbolTable;
import edu.kit.iti.algover.parser.DafnyParserException;
import edu.kit.iti.algover.proof.PVC;
import edu.kit.iti.algover.proof.PVCCollection;
import edu.kit.iti.algover.proof.Proof;
import edu.kit.iti.algover.proof.ProofStatus;
import edu.kit.iti.algover.script.exceptions.ScriptCommandNotApplicableException;
import edu.kit.iti.algover.term.FunctionSymbol;
import edu.kit.iti.algover.term.Sequent;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.term.parser.TermParser;
import edu.kit.iti.algover.util.TestUtil;
import edu.kit.iti.algover.util.Util;
import org.junit.Assert;
import org.junit.Before;
import org.junit.Test;

import java.io.File;
import java.io.IOException;
import java.net.URL;
import java.util.ArrayList;
import java.util.Collection;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

/**
 * Tests for the methods for ProjectManagement
 */
public class DafnyProjectManagerTest {

    @Test
    public void testDafnyProjectConfig() throws IOException, DafnyParserException {

        URL res = getClass().getResource("dafnyProject.dfy");
        assertEquals("test resources must be in file system", "file", res.getProtocol());

        DafnyProjectManager man = new DafnyProjectManager(new File(res.getPath()));
        man.reload();
        Configuration config = man.getConfiguration();

        assertEquals("[dafnyProject.dfy, s1.dfy, s2.dfy]",
                Util.map(config.getDafnyFiles(), f -> f.getName()).toString());

        assertEquals("[i1.dfy, i2.dfy]",
                Util.map(config.getLibFiles(), f -> f.getName()).toString());

    }


}
