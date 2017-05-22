/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.project;

import static org.junit.Assert.assertEquals;

import java.io.File;
import java.util.Collection;
import java.util.LinkedList;
import java.util.List;

import org.junit.Before;
import org.junit.Test;

import edu.kit.iti.algover.dafnystructures.DafnyFile;
import edu.kit.iti.algover.dafnystructures.DafnyMethod;
import edu.kit.iti.algover.settings.ProjectSettings;


/**
 * Created by sarah on 8/18/16.
 * */

public class ProjectTest {
    Project p = null;

    String testDir = "modules/core/test-res/edu/kit/iti/algover/project";

    @Before
    public void prepare() throws Exception {

        final File f1 = new File(testDir);

        ProjectBuilder pb = new ProjectBuilder();
        pb.setDir(f1);
        Project p = pb.build();
        this.p = p;

    }
    @Test
    public void testProjectImports(){

        List<DafnyFile> dafnyFiles = p.getDafnyFiles();
        List<File> filesToTest = new LinkedList<>();
        filesToTest.add(new File(testDir+File.separator+"test.dfy"));
        filesToTest.add(new File(testDir+File.separator+"test2.dfy"));
        assertEquals(dafnyFiles, filesToTest);
    }

    @Test
    public void testSettings(){
        ProjectSettings testSettings = p.getSettings();
        String value = testSettings.getValue(ProjectSettings.DAFNY_TIMEOUT);
        assertEquals(Integer.parseInt(value), 24);
    }

    @Test
    public void testMethodExtraction(){
        assertEquals(p.getClasses().size(), 1);
        Collection<DafnyMethod> methods = p.getClass("foo3").getMethods();

        List<String> methodNames = new LinkedList<>();
        List<String> methodsString = new LinkedList<>();
        methodsString.add("arrayUpdate");
        methodsString.add("foo");
        assertEquals(methods.size(), 2);
        for(DafnyMethod m: methods){
            methodNames.add(m.getName());
        }
        assertEquals(methodsString, methodNames);


    }
    //TODO test that classes and functions are correctly extracted
}
