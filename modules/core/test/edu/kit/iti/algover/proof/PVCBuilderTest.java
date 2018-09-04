/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.proof;

import java.io.FileNotFoundException;
import java.io.InputStream;
import java.util.Arrays;
import java.util.Collection;

import edu.kit.iti.algover.util.ImmutableList;
import edu.kit.iti.algover.util.Util;

import edu.kit.iti.algover.parser.DafnyTree;
import edu.kit.iti.algover.parser.ParserTest;
import edu.kit.iti.algover.project.Project;
import edu.kit.iti.algover.util.TestUtil;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameter;
import org.junit.runners.Parameterized.Parameters;

import static org.junit.Assert.*;

/*
 * This test checks that files are parseable and can produce good projects.
 * (PVC generation works w/o exception).
 *
 * The actual content is not checked because it would be incomprehensible.
 */
@RunWith(Parameterized.class)
public class PVCBuilderTest {

    @Parameter
    public String filename;

    @Parameters(name = "{0}")
    public static Collection<? extends Object> parameters() throws Exception {

        InputStream is = PVCBuilderTest.class.getResourceAsStream("pvcBuilder/INDEX");
        if (is == null) {
            fail("File not found: pvcBuilder/INDEX");
        }

        ImmutableList<String> filenames = ImmutableList.from(Util.streamToString(is).split("\n"));
        filenames = filenames.filter(x -> !x.isEmpty() && !x.trim().startsWith("#"));

        return filenames.asCollection();
    }

    @Test
    public void test() throws Exception {

        InputStream is = PVCBuilderTest.class.getResourceAsStream("pvcBuilder/" + filename);

        if (is == null) {
            throw new FileNotFoundException("File not found: pvcBuilder/" + filename);
        }

        DafnyTree fileTree = ParserTest.parseFile(is);
        is.close();

        Project project = TestUtil.mockProject(fileTree);
        PVCGroup pvcGroup = project.getAllPVCs();

        // success if no exception occurs!
    }

}
