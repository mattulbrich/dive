/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.dafnystructures;

import static org.junit.Assert.assertEquals;

import java.io.File;
import java.io.FileNotFoundException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

import org.junit.Test;

import edu.kit.iti.algover.parser.DafnyTree;
import edu.kit.iti.algover.parser.ParserTest;
import edu.kit.iti.algover.project.Project;
import edu.kit.iti.algover.project.ProjectBuilder;


// deactivated for now ... not clear how this works

public class DafnyTreeToDeclVisitorTest {

    @Test
    public void test() throws Exception {
        DafnyTree tree =
                ParserTest.parseFile(getClass().getResourceAsStream("declTest.dfy"));

        ProjectBuilder builder = new ProjectBuilder();
        builder.setDir(new File("dir"));
        builder.setScriptFile("project.script");
        Project project = builder.build();

        Path tempDir = Files.createTempDirectory("dafny-algover");

        List<DafnyClass> classes = new ArrayList<>(project.getClasses());
        assertEquals(1, classes.size());
        {
        DafnyClass clazz = classes.get(0);
        }

        Collection<DafnyMethod> methods = project.getMethods();
        assertEquals(2, methods.size());
    }

    // threw a NullPointerException, should throw clear exception
    @Test(expected = FileNotFoundException.class)
    public void testNonexistingDirectory() throws Exception {
        ProjectBuilder builder = new ProjectBuilder();
        builder.setDir(new File("nonexistingdirectory"));
        builder.build();
    }

}
