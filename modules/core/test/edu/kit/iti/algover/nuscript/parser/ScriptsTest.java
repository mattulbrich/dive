package edu.kit.iti.algover.nuscript.parser;

import edu.kit.iti.algover.nuscript.ScriptAST.Script;
import org.junit.Assert;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameter;
import org.junit.runners.Parameterized.Parameters;

import java.io.FileNotFoundException;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.List;

import static org.junit.Assert.*;

@RunWith(Parameterized.class)
public class ScriptsTest {


    private static final Path TEST_DIR =
            Paths.get("test-res","edu", "kit", "iti", "algover", "nuscript", "parser");

    private static final boolean VERBOSE =
            Boolean.getBoolean("algover.test.verbose");

    @Parameter(0)
    public Path path;

    @Parameter(1)
    public String filename;

    @Parameters(name= "{1}")
    public static Iterable<Object[]> data() throws IOException {
        List<Object[]> result = new ArrayList<>();
        Files.list(TEST_DIR).forEach(p -> {
            if (p.getFileName().toString().endsWith(".script"))
                result.add(new Object[]{p, p.getFileName().toString()});
        });
        return result;
    }

    @Test
    public void test() throws IOException {
        if (!Files.exists(path)) {
            throw new FileNotFoundException(path.toAbsolutePath().toString());
        }

        Script script = Scripts.parseScript(path);
        Assert.assertNotNull(script);

        Path expectedPath = path.getParent().resolve(filename + ".expected");
        if(!Files.exists(expectedPath)) {
            expectedPath = path;
        }

        String expected = Files.readString(expectedPath);

        assertEquals(expected.trim(), script.toString().trim());
    }

}