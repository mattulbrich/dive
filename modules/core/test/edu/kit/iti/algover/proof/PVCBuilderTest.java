/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.proof;

import java.io.File;
import java.io.InputStream;

import org.junit.Test;

import edu.kit.iti.algover.parser.DafnyTree;
import edu.kit.iti.algover.parser.ParserTest;
import edu.kit.iti.algover.project.Project;
import edu.kit.iti.algover.util.TestUtil;

public class PVCBuilderTest {

    private static final File FILE =
            new File("modules/core/test-res/edu/kit/iti/algover/proof/proj1");

    // This is more an integration test ... just should not throw exceptions.
    // Sum and max is the first benchmark milestone for September 17
    @Test
    public void testSumAndMax() throws Exception {

        InputStream is = ParserTest.class.getResourceAsStream("full/sumandmax.dfy");
        DafnyTree fileTree = ParserTest.parseFile(is);
        Project project = TestUtil.mockProject(fileTree);

        project.getAllVerificationConditions();
    }

}
