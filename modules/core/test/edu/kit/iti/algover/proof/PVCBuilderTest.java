/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.proof;

import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.InputStream;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.Date;
import java.util.List;
import java.util.Properties;

import edu.kit.iti.algover.parser.DafnyException;
import edu.kit.iti.algover.parser.DafnyParserException;
import edu.kit.iti.algover.project.ProjectBuilder;
import edu.kit.iti.algover.settings.ProjectSettings;
import edu.kit.iti.algover.term.Sequent;
import edu.kit.iti.algover.util.Util;
import org.junit.Test;

import edu.kit.iti.algover.parser.DafnyTree;
import edu.kit.iti.algover.parser.ParserTest;
import edu.kit.iti.algover.project.Project;
import edu.kit.iti.algover.util.TestUtil;
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

    public static final String SEQUENTER_KEY = "sequenter";

    @Parameter
    public String filename;

    @Parameters(name = "{0}")
    public static Collection<? extends Object> parameters() throws Exception {

        InputStream is = PVCBuilderTest.class.getResourceAsStream("pvcBuilder/INDEX");
        if (is == null) {
            fail("File not found: pvcBuilder/INDEX");
        }

        String[] filenames = Util.streamToString(is).split("\n");
        return Arrays.asList(filenames);
    }

    @Test
    public void test() throws Exception {

        InputStream is = PVCBuilderTest.class.getResourceAsStream("pvcBuilder/" + filename);
        DafnyTree fileTree = ParserTest.parseFile(is);
        is.close();

        Project project = TestUtil.mockProject(fileTree);
        PVCGroup pvcGroup = project.getAllPVCs();

        // success if no exception occurs!
    }

}
