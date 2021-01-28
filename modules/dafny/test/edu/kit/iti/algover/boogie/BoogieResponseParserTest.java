package edu.kit.iti.algover.boogie;

import org.junit.Test;

import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Arrays;

import static org.junit.Assert.*;

public class BoogieResponseParserTest {

    private static final String CODE =
            "procedure Test1()\n  ensures false;\n{\n  assume false;\n}\n\n\n" +
            "procedure Test2()\n  ensures false;\n{\n  assert true;\n}\n" +
            "procedure Test3()\n  ensures false;\n{\n  assume false;\n}\n";

    // discovered a bug.
    @Test
    public void testBoogieResponse() throws Exception {

        // The boogie code is stored in a temporary file
        Path tmpFile = Files.createTempFile("dive-test-", ".bpl");

        // write prelude, obligation and add. code
        Files.write(tmpFile, Arrays.asList(BoogieTranslation.PRELUDE, CODE, ""));

        Process proc = BoogieProcess.buildProcess(tmpFile);

        BoogieResponseParser brp = new BoogieResponseParser(CODE);
        brp.readFrom(proc.getInputStream());

        assertTrue(brp.isConsistent());
        assertEquals("[0, 2]", brp.getVerifiedProcedures().toString());
        assertEquals("[1]", brp.getFailedProcedures().toString());

        // Delete file on success
        Files.delete(tmpFile);

    }
}