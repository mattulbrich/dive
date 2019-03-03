/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.project;

import edu.kit.iti.algover.dafnystructures.DafnyClass;
import edu.kit.iti.algover.dafnystructures.DafnyFile;
import edu.kit.iti.algover.dafnystructures.DafnyFunction;
import edu.kit.iti.algover.dafnystructures.DafnyMethod;
import edu.kit.iti.algover.parser.DafnyParserException;
import edu.kit.iti.algover.proof.PVC;
import edu.kit.iti.algover.rules.ProofRule;
import edu.kit.iti.algover.rules.impl.DafnyRule;
import edu.kit.iti.algover.settings.ProjectSettings;
import edu.kit.iti.algover.util.FormatException;
import edu.kit.iti.algover.util.TestUtil;
import org.junit.Before;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.ExpectedException;

import java.io.File;
import java.io.IOException;
import java.lang.reflect.Field;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.List;
import java.util.Map;
import java.util.NoSuchElementException;
import java.util.stream.Collectors;

import static org.junit.Assert.*;
import org.xml.sax.SAXException;

import javax.xml.bind.JAXBException;


/**
 * Created by sarah on 8/18/16.
 * */

public class ProjectTest {
    static final String testDir = "modules/core/test-res/edu/kit/iti/algover/project";
    static final String CONFIG = "config.xml";
    Project p = null;

    @Rule
    public final ExpectedException exception = ExpectedException.none();

    @Before
    public void prepare() throws Exception {

        final File f1 = new File(testDir);

        ProjectBuilder pb = new ProjectBuilder();
        pb.setDir(f1);
        XMLProjectManager.parseProjectConfigurationFile(f1, CONFIG, pb);
        Project p = pb.build();
        this.p = p;

    }
    @Test
    public void testProjectImports(){
        List<DafnyFile> dafnyFiles = p.getDafnyFiles();
        System.out.println(dafnyFiles.stream().map(DafnyFile::getFilename).collect(Collectors.toList()));
        assertEquals(3, dafnyFiles.size());
        assertEquals(testDir + "/test3.dfy", dafnyFiles.get(0).getName());
        assertTrue(dafnyFiles.get(0).isInLibrary());
        assertEquals(testDir + "/test.dfy", dafnyFiles.get(1).getName());
        assertFalse(dafnyFiles.get(1).isInLibrary());
        assertEquals(testDir + "/test2.dfy", dafnyFiles.get(2).getName());
        assertFalse(dafnyFiles.get(2).isInLibrary());
    }

    @Test
    public void testSettings() throws FormatException {
        ProjectSettings testSettings = p.getSettings();
        testSettings.validate();
        String value = testSettings.getString(ProjectSettings.DAFNY_TIMEOUT);
        assertEquals(24, Integer.parseInt(value));
        assertEquals(24, testSettings.getInt(ProjectSettings.DAFNY_TIMEOUT));
        assertEquals(true, testSettings.getBoolean(ProjectSettings.SYMBEX_UNROLL_LOOPS));
    }

    @SuppressWarnings({"rawtypes", "unchecked"})
    @Test
    public void testSettingsInsane() throws Exception {
        ProjectSettings testSettings = p.getSettings();

        Field fieldSet = ProjectSettings.class.getDeclaredField("set");
        fieldSet.setAccessible(true);
        ((Map) fieldSet.get(testSettings)).put(ProjectSettings.DAFNY_TIMEOUT, "No integer");

        exception.expect(FormatException.class);
        testSettings.validate();
    }

    @Test
    public void testConfigurationValidation() throws IOException, FormatException, JAXBException, SAXException {
        final File f1 = new File(testDir);

        ProjectBuilder pb = new ProjectBuilder();
        pb.setDir(f1);
        // was: pb.parseProjectConfigurationFile();
        XMLProjectManager.parseProjectConfigurationFile(f1, CONFIG, pb);
        pb.validateProjectConfiguration();
    }

    @Test
    public void testMethodExtraction(){
        assertEquals(2, p.getClasses().size());

        DafnyClass foo = p.getClass("foo");
        assertTrue(foo.isInLibrary());

        DafnyClass foo3 = p.getClass("foo3");
        assertFalse(foo3.isInLibrary());

        assertEquals(2, foo3.getMethods().size());
        assertNotNull(foo3.getMethod("arrayUpdate"));
        assertNotNull(foo3.getMethod("foo"));
    }

    @Test
    public void testPVCgeneration() {
        PVC pvc1 = p.getPVCByName("single/Post");
        assertNotNull(pvc1);

        p.getAllPVCs();
        PVC pvc2 = p.getPVCByName("single/Post");
        assertSame("Second request should give same pvc", pvc1, pvc2);
    }

    @Test
    public void testPVCByName() {
        assertNotNull(p.getPVCByName("single/Post"));
    }

    //TODO test that classes and functions are correctly extracted

    @Test
    public void testLemmaFiltering() throws Exception {

        final File f = new File(testDir, "lemma_test");
        ProjectBuilder pb = new ProjectBuilder();
        pb.setDir(f);
        // pb.parseProjectConfigurationFile();
        XMLProjectManager.parseProjectConfigurationFile(f, CONFIG, pb);
        Project p = pb.build();

        int totalRuleCount;

        {
            Collection<ProofRule> allProofRules = p.getAllProofRules();
            totalRuleCount = allProofRules.size();
            List<String> dafnyRules = allProofRules.stream()
                    .filter(x -> x instanceof DafnyRule)
                    .map(ProofRule::getName)
                    .collect(Collectors.toList());

            List<String> expected = Arrays.asList(
                    "liblemma11", "liblemma12", "liblemma13",
                    "liblemma21", "liblemma22", "liblemma23",
                    "srclemma11", "srclemma12", "srclemma13",
                    "srclemma21", "srclemma22", "srclemma23");

            assertEquals(expected, dafnyRules);
        }
        {
            Collection<ProofRule> filtered = p.getProofRules(p.getPVCByName("liblemma21/Post"));
            // 9 rules have been filtered;
            assertEquals(totalRuleCount - 9, filtered.size());
            List<String> dafnyRules = filtered.stream()
                    .filter(x -> x instanceof DafnyRule)
                    .map(ProofRule::getName)
                    .collect(Collectors.toList());

            List<String> expected = Arrays.asList(
                    "liblemma11", "liblemma12", "liblemma13");
            assertEquals(expected, dafnyRules);
        }
        {
            Collection<ProofRule> filtered = p.getProofRules(p.getPVCByName("srclemma21/Post"));
            // 3 rules have been filtered;
            assertEquals(totalRuleCount - 3, filtered.size());
            List<String> dafnyRules = filtered.stream()
                    .filter(x -> x instanceof DafnyRule)
                    .map(ProofRule::getName)
                    .collect(Collectors.toList());

            List<String> expected = Arrays.asList(
                    "liblemma11", "liblemma12", "liblemma13",
                    "liblemma21", "liblemma22", "liblemma23",
                    "srclemma11", "srclemma12", "srclemma13");
            assertEquals(expected, dafnyRules);
        }
    }

    // after a bugfix
    @Test
    public void testGetPVCCollection() throws Exception {
        Project p = TestUtil.mockProject(
                "class C { method m() {} function f(): int {1} } " +
                        "method n() {} " +
                        "function g(): int {2}");
        DafnyMethod m = p.getClass("C").getMethod("m");
        assertNotNull(p.getPVCsFor(m));
        DafnyFunction f = p.getClass("C").getFunction("f");
        assertNotNull(p.getPVCsFor(f));
        DafnyMethod n = p.getMethod("n");
        assertNotNull(p.getPVCsFor(n));
        DafnyFunction g = p.getFunction("g");
        assertNotNull(p.getPVCsFor(g));

        Project q = TestUtil.mockProject("method q() {}");
        DafnyMethod unknown = q.getMethod("q");
        try {
            p.getPVCsFor(unknown);
            fail("Should have thrown");
        } catch(NoSuchElementException ex) {
        }
    }
}
