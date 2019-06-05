/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.project;

import edu.kit.iti.algover.settings.ProjectSettings;
import edu.kit.iti.algover.util.TestUtil;
import edu.kit.iti.algover.util.Util;
import org.junit.After;
import org.junit.Before;
import org.junit.Test;

import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.net.URL;
import java.util.Arrays;
import java.util.HashMap;
import java.util.Map;

import static org.junit.Assert.*;

public class DafnyProjectConfigurationChangerTest {

    private static String IN_RESOURCE = "dafnyBeforeConfigRewrite.dfy";
    private static String OUT_RESOURCE = "dafnyAfterConfigRewrite.dfy";
    private static String OUT_FRESH_RESOURCE = "dafnyAfterConfigFirstWrite.dfy";

    private File tmpFile;

    @Before
    public void setup() throws Exception {
        this.tmpFile = File.createTempFile("Algover", ".dfy");
    }

    @After
    public void tearDown() throws Exception {
        this.tmpFile.delete();
    }

    @Test
    public void testExisting() throws Exception {

        InputStream in = getClass().getResourceAsStream(IN_RESOURCE);
        FileOutputStream out = new FileOutputStream(tmpFile);
        Util.drainStream(in, out);
        in.close();
        out.close();

        System.err.println("Temp file: " + tmpFile);


        Configuration c = new Configuration();
        c.setDafnyFiles(Arrays.asList(new File("file1.dfy"),
                new File("/absolute/file2.dfy"),
                new File("with spaces.dfy")));

        c.setLibFiles(Arrays.asList(new File("lib1.dfy"),
                new File("/absolute/lib2.dfy"),
                new File("with spaces lib.dfy")));

        Map<String, String> map = new HashMap<>();
        map.put(ProjectSettings.DAFNY_TIMEOUT, "100");
        map.put(ProjectSettings.DEFAULT_SCRIPT, "boogie;");
        c.setSettings(map);

        DafnyProjectConfigurationChanger.saveConfiguration(c, tmpFile);

        URL expectedURL = getClass().getResource(OUT_RESOURCE);
        assertEquals( "Test cases must be in file system", "file", expectedURL.getProtocol());
        File expectedFile = new File(expectedURL.toURI());

        TestUtil.assertSameTextFiles(expectedFile, tmpFile);

        // Check idempotence
        DafnyProjectConfigurationChanger.saveConfiguration(c, tmpFile);
        TestUtil.assertSameTextFiles(expectedFile, tmpFile);
    }

    @Test
    public void testNonExisting() throws Exception {

        System.err.println("Temp file: " + tmpFile);

        Configuration c = new Configuration();
        c.setDafnyFiles(Arrays.asList(new File("file1.dfy"),
                new File("/absolute/file2.dfy"),
                new File("with spaces.dfy")));

        c.setLibFiles(Arrays.asList(new File("lib1.dfy"),
                new File("/absolute/lib2.dfy"),
                new File("with spaces lib.dfy")));

        Map<String, String> map = new HashMap<>();
        map.put(ProjectSettings.DAFNY_TIMEOUT, "100");
        map.put(ProjectSettings.DEFAULT_SCRIPT, "boogie;");
        c.setSettings(map);

        DafnyProjectConfigurationChanger.saveConfiguration(c, tmpFile);

        URL expectedURL = getClass().getResource(OUT_FRESH_RESOURCE);
        assertEquals( "Test cases must be in file system", "file", expectedURL.getProtocol());
        File expectedFile = new File(expectedURL.toURI());

        TestUtil.assertSameTextFiles(expectedFile, tmpFile);
    }


}