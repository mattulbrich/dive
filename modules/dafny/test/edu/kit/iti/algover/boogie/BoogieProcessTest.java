/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 *
 */

package edu.kit.iti.algover.boogie;

import edu.kit.iti.algover.data.BuiltinSymbols;
import edu.kit.iti.algover.data.SymbolTable;
import edu.kit.iti.algover.project.Project;
import edu.kit.iti.algover.term.FunctionSymbol;
import edu.kit.iti.algover.term.Sequent;
import edu.kit.iti.algover.term.Sort;
import edu.kit.iti.algover.term.parser.TermParser;
import edu.kit.iti.algover.util.LineProperties;
import edu.kit.iti.algover.util.TestUtil;
import edu.kit.iti.algover.util.TreeUtil;
import edu.kit.iti.algover.util.Util;
import org.junit.Assume;
import org.junit.Before;
import org.junit.FixMethodOrder;
import org.junit.Ignore;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.MethodSorters;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameter;
import org.junit.runners.Parameterized.Parameters;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.net.MalformedURLException;
import java.net.URL;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.function.Function;

import static org.junit.Assert.assertEquals;

@FixMethodOrder(MethodSorters.NAME_ASCENDING)
@RunWith(Parameterized.class)
public class BoogieProcessTest {

    @Parameter
    public URL url;

    @Parameter(1)
    public String name;

    private SymbolTable table = new BuiltinSymbols();

    private Sequent sequent;

    private boolean expectedResult;

    private String expectedTranslation;

    private String project;

    private String additionalBoogieCode;

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

        LineProperties props = new LineProperties();
        props.read(url.openStream());

        for (String line : props.getLines("decls")) {
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

        this.sequent = TermParser.parseSequent(table, props.get("sequent"));

        this.expectedResult = props.getOrDefault("result", "fail").equalsIgnoreCase("prove");

        this.expectedTranslation = props.get("translation");

        this.project = props.getOrDefault("project", "method m() {}");

        this.additionalBoogieCode = props.getOrDefault("additionalBoogie", "");
    }

    @Test
    public void testBoogie() throws Exception {
        Project p = TestUtil.mockProject(project);
        BoogieProcess process = new BoogieProcess(p);
        process.setSequent(sequent);
        process.setSymbolTable(table);
        process.setAdditionalBoogieText(additionalBoogieCode);

        assertEquals(expectedResult, process.callBoogie());

        if (expectedTranslation == null) {
            return;
        }

        String actualTranslation = process.produceObligation().toString().trim();

        if (!expectedTranslation.equals(actualTranslation)) {
            System.out.println(">>> " + name);
            System.out.println("### translation:");
            System.out.println(actualTranslation);
            System.out.println("# expected ");
            System.out.println(expectedTranslation);
        }

        assertEquals(expectedTranslation, actualTranslation);
    }
}