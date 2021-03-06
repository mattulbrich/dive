/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.script;


import edu.kit.iti.algover.nuscript.ScriptAST;
import edu.kit.iti.algover.nuscript.parser.Scripts;
import org.junit.Assert;
import org.junit.Ignore;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameter;

import java.io.*;
import java.nio.file.Files;
import java.util.ArrayList;
import java.util.List;

/**
 * IMPORTANT
 * This test is ignored because atm refactoring is going
 * on on another branch and recent state is not merged completly with master yet
 * Test class for testing the script parser
 */

// REVIEW: Resolve this warning suppression!

@RunWith(Parameterized.class)
@Ignore
public class ScriptParserTest {

    static final String testDir = ("test-res/edu/kit/iti/algover/script/parser").replace('/', File.separatorChar);

    @Parameter(0)
    public File file;

    @Parameter(1)
    public String name;

    @Parameterized.Parameters(name = "{1}")
    public static Iterable<Object[]> data() {
        File dir = new File(testDir);
        List<Object[]> result = new ArrayList<>();
        for (File file : dir.listFiles((FilenameFilter)((d,name) -> name.endsWith(".script")))) {
            result.add(new Object[]{ file, file.getName() });
        }
        return result;
    }

    public ScriptParserTest() {
    }

    @Test
    public void testParseScript() throws Exception {
        if (!file.exists()) {
            throw new FileNotFoundException(file.getAbsolutePath());
        }

        ScriptAST script = Scripts.parseScript(file);
        Assert.assertNotNull(script);

        File file2 = new File(file.getAbsoluteFile() + ".expected");
        File expectedFile = file;
        if(file2.exists()) {
            expectedFile = file2;
        }

        String expected = Files.readString(expectedFile.toPath());
        Assert.assertEquals(expected.trim(), script.toString().trim());
    }


}
