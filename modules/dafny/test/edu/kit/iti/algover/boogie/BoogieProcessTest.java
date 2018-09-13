/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 *
 */

package edu.kit.iti.algover.boogie;

import edu.kit.iti.algover.data.BuiltinSymbols;
import edu.kit.iti.algover.data.SymbolTable;
import edu.kit.iti.algover.term.FunctionSymbol;
import edu.kit.iti.algover.term.Sequent;
import edu.kit.iti.algover.term.Sort;
import edu.kit.iti.algover.term.parser.TermParser;
import edu.kit.iti.algover.util.TestUtil;
import edu.kit.iti.algover.util.TreeUtil;
import edu.kit.iti.algover.util.Util;
import org.junit.Before;
import org.junit.Ignore;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameter;
import org.junit.runners.Parameterized.Parameters;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.net.MalformedURLException;
import java.net.URL;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.function.Function;

import static org.junit.Assert.assertEquals;

@RunWith(Parameterized.class)
public class BoogieProcessTest {

    @Parameter
    public URL url;

    @Parameter(1)
    public String name;

    private SymbolTable table = new BuiltinSymbols();

    private Sequent sequent;

    private boolean expectedResult;

    private List<String> expectedTranslation;

    protected static List<Object[]> parametersFor(String resource) throws MalformedURLException {
        URL res = BoogieProcess.class.getResource(resource);
        List<URL> list = TestUtil.getResourcesIn(res, "boogie", false);
        return Util.map(list, l->new Object[] {l, l.getFile().substring(res.getFile().length())});
    }

    @Parameters(name = "{1}")
    public static List<Object[]> parameters() throws MalformedURLException {
        return parametersFor("");
    }

    @Before
    public void setup() throws Exception {

        BufferedReader br = new BufferedReader(new InputStreamReader(url.openStream()));
        String line;

        while ((line = br.readLine()) != null) {
            if (line.startsWith("----")) {
                break;
            }
            String[] parts = line.split(" *(\\*|:|->) *");
            String name = parts[0];
            Sort resultSort = Sort.parseSort(parts[parts.length - 1]);
            Sort args[] = new Sort[parts.length - 2];
            for (int i = 0; i < args.length; i++) {
                args[i] = Sort.parseSort(parts[i + 1]);
            }
            FunctionSymbol fs = new FunctionSymbol(name, resultSort, args);
            table.addFunctionSymbol(fs);
        }

        StringBuilder sb = new StringBuilder();
        while ((line = br.readLine()) != null) {
            if (line.startsWith("----")) {
                break;
            }
            sb.append(line).append("\n");
        }

        this.sequent = TermParser.parseSequent(table, sb.toString());

        this.expectedResult = br.readLine().trim().equalsIgnoreCase("unsat");

        this.expectedTranslation = new ArrayList<>();

        while ((line = br.readLine()) != null) {
            if (line.startsWith("----")) {
                // The remainder of the file is comment
                break;
            }
            this.expectedTranslation.add(line);
        }
    }

    @Test
    public void testTranslation() throws Exception {

        BoogieProcess process = new BoogieProcess();
        process.setSequent(sequent);
        process.setSymbolTable(table);
        String obligation = process.produceObligation().toString();

        System.out.println(">>>" + name);
        System.out.println(obligation);
        System.out.flush();

        String[] lines = obligation.split("\n");

        List<String> actual = Arrays.asList(lines);

        assertEquals(Util.join(expectedTranslation, "\n"),
                Util.join(actual, "\n"));

    }

    @Test // @Ignore
    public void testResult() throws Exception {
        BoogieProcess process = new BoogieProcess();
        process.setSequent(sequent);
        process.setSymbolTable(table);

        assertEquals(expectedResult, process.callBoogie());

    }
}