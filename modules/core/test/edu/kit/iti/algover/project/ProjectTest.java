/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.project;

import static org.junit.Assert.*;

import java.io.File;
import java.util.List;

import org.junit.Before;
import org.junit.Test;

import edu.kit.iti.algover.dafnystructures.DafnyClass;
import edu.kit.iti.algover.dafnystructures.DafnyFile;
import edu.kit.iti.algover.settings.ProjectSettings;


/**
 * Created by sarah on 8/18/16.
 * */

public class ProjectTest {
    Project p = null;

    // REVIEW: Why not static final?
    String testDir = "modules/core/test-res/edu/kit/iti/algover/project";

    @Before
    public void prepare() throws Exception {

        final File f1 = new File(testDir);

        ProjectBuilder pb = new ProjectBuilder();
        pb.setDir(f1);
        pb.parseScript();
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
    public void testSettings(){
        ProjectSettings testSettings = p.getSettings();
        String value = testSettings.getValue(ProjectSettings.DAFNY_TIMEOUT);
        assertEquals(Integer.parseInt(value), 24);
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

    //TODO test that classes and functions are correctly extracted
}
