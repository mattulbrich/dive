/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 *
 */

package edu.kit.iti.algover.boogie;


import edu.kit.iti.algover.project.DafnyProjectManager;
import edu.kit.iti.algover.project.Project;
import edu.kit.iti.algover.project.ProjectBuilder;
import edu.kit.iti.algover.proof.PVC;
import edu.kit.iti.algover.term.Sequent;
import edu.kit.iti.algover.util.TestUtil;
import edu.kit.iti.algover.util.Util;
import static org.junit.Assert.*;
import org.junit.Before;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameter;
import org.junit.runners.Parameterized.Parameters;

import java.io.File;
import java.net.MalformedURLException;
import java.net.URL;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.Arrays;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.Stream;

@RunWith(Parameterized.class)
public class BoogieFunctionDefinitionTest {

    @Parameter
    public URL url;

    @Parameter(1)
    public String name;
    private List<String> expectedLines;
    private Sequent sequent;
    private Project project;
    private PVC pvc;

    @Parameters(name = "{1}")
    public static List<Object[]> parameters() throws MalformedURLException {
//        URL res = BoogieProcess.class.getResource("dafnyFunctions");
//        List<URL> list = TestUtil.getResourcesIn(res, "dfy", false);
//        return Util.map(list, l->new Object[] {l, l.getFile().substring(res.getFile().length())});
        return null;
    }

    @Before
    public void setup() throws Exception {

        assertTrue(url.getProtocol().equals("file"));
        String path = url.getPath();
        DafnyProjectManager pm = new DafnyProjectManager(new File(path));
        pm.reload();
        this.project = pm.getProject();
        this.pvc = project.getPVCByName("test/Post");
        this.sequent = pvc.getSequent();
        this.expectedLines = Files.lines(Paths.get(path + ".bpl-expected")).collect(Collectors.toList());
    }

    @Test
    public void test() throws Exception {
        BoogieProcess process = new BoogieProcess(project);
        process.setSequent(sequent);
        process.setSymbolTable(pvc.getSymbolTable());

        String obligation = process.getObligation().toString();
        Set<String> lines = new HashSet<>(
                Util.map(Arrays.asList(obligation.split("\n")), String::trim));

        for (String expectedLine : expectedLines) {
            expectedLine = expectedLine.trim();
            if(expectedLine.isEmpty() || expectedLine.startsWith("#")) {
                // no comments
                continue;
            }
            if(!lines.contains(expectedLine)) {
                System.out.println(obligation);
                fail("Line '" + expectedLine + "' not in Boogie translation");
            }
        }
    }
}
