/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 *
 */

package edu.kit.iti.algover.smttrans.translate;

import edu.kit.iti.algover.dafnystructures.DafnyDecl;
import edu.kit.iti.algover.data.BuiltinSymbols;
import edu.kit.iti.algover.data.MapSymbolTable;
import edu.kit.iti.algover.data.SymbolTable;
import edu.kit.iti.algover.parser.DafnyException;
import edu.kit.iti.algover.parser.DafnyParserException;
import edu.kit.iti.algover.project.Project;
import edu.kit.iti.algover.project.ProjectBuilder;
import edu.kit.iti.algover.proof.MethodPVCBuilder;
import edu.kit.iti.algover.proof.MockPVCBuilder;
import edu.kit.iti.algover.proof.PVC;
import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.rules.RuleException;
import edu.kit.iti.algover.rules.impl.Z3Rule;
import edu.kit.iti.algover.smttrans.access.Response;
import edu.kit.iti.algover.smttrans.access.SolverParameter;
import edu.kit.iti.algover.smttrans.access.SolverResponse;
import edu.kit.iti.algover.smttrans.access.Z3Access;
import edu.kit.iti.algover.term.FunctionSymbol;
import edu.kit.iti.algover.term.Sequent;
import edu.kit.iti.algover.term.Sort;
import edu.kit.iti.algover.term.parser.TermParser;
import edu.kit.iti.algover.util.TreeUtil;

import org.junit.Assert;
import org.junit.Before;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameter;
import org.junit.runners.Parameterized.Parameters;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.util.Arrays;
import java.util.Collection;

import static org.junit.Assert.*;

@RunWith(Parameterized.class)
public class SeqUnitTest {

    @Parameter
    public String name;

    private SymbolTable st;

    private Sequent sequent;

    @Parameters(name = "{0}")
    public static Object[] data() {
        return new Object[] { "seq" };
    }

    @Before
    public void readAndParse() throws IOException, DafnyParserException, DafnyException {

        st = new BuiltinSymbols();

        InputStream stream = getClass().getResourceAsStream(name + ".smt-test");
        BufferedReader r = new BufferedReader(new InputStreamReader(stream));

        String line;
        while((line=r.readLine()) != null) {
            line = line.trim();
            if (line.startsWith("#") || line.isEmpty()) {
                continue;
            }

            if(line.equals("---")) {
                break;
            }

            String[] parts = line.split(" *: *", 2);

            Sort s = TreeUtil.parseSort(parts[1]);
            st.addFunctionSymbol(new FunctionSymbol(parts[0], s));
        }

        StringBuilder sb = new StringBuilder();
        while((line=r.readLine()) != null) {
            sb.append(line).append("\n");
        }

        this.sequent = TermParser.parseSequent(st, sb.toString());
    }

    @Test
    public void verifyZ3() {
        Z3Rule rule = new Z3Rule();
        Z3Access z3Access = new Z3Access();
        String smt = rule.testRule(sequent, st);

        SolverParameter p = new SolverParameter(smt, 3, true);
        SolverResponse r1 = z3Access.accessSolver(p);
        Assert.assertEquals(Response.UNSAT, r1.getResponse());



        
        
    }

    @Test
    public void verifyCVC() {

    }

}