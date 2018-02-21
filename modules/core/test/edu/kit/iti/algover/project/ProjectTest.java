/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.project;

import edu.kit.iti.algover.dafnystructures.DafnyClass;
import edu.kit.iti.algover.dafnystructures.DafnyFile;
import edu.kit.iti.algover.proof.PVC;
import edu.kit.iti.algover.settings.ProjectSettings;
import edu.kit.iti.algover.util.FormatException;
import org.junit.Before;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.ExpectedException;

import java.io.File;
import java.io.IOException;
import java.lang.reflect.Field;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;
import java.util.Map;

import static org.junit.Assert.*;
import org.xml.sax.SAXException;

import javax.xml.bind.JAXBException;


/**
 * Created by sarah on 8/18/16.
 * */

public class ProjectTest {
    static final String testDir = "modules/core/test-res/edu/kit/iti/algover/project";
    Project p = null;

    @Rule
    public final ExpectedException exception = ExpectedException.none();

    @Before
    public void prepare() throws Exception {

        final File f1 = new File(testDir);

        ProjectBuilder pb = new ProjectBuilder();
        pb.setDir(f1);
        pb.parseProjectConfigurationFile();
        Project p = pb.build();
        this.p = p;

    }
    @Test
    public void testProjectImports(){
        List<DafnyFile> dafnyFiles = p.getDafnyFiles();
        assertEquals(3, dafnyFiles.size());
        assertEquals("test.dfy", dafnyFiles.get(0).getName());
        assertFalse(dafnyFiles.get(0).isInLibrary());
        assertEquals("test2.dfy", dafnyFiles.get(1).getName());
        assertFalse(dafnyFiles.get(1).isInLibrary());
        assertEquals("test3.dfy", dafnyFiles.get(2).getName());
        assertTrue(dafnyFiles.get(2).isInLibrary());
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
        pb.parseProjectConfigurationFile();
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
}
