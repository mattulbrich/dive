/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.cli;

import edu.kit.iti.algover.parser.DafnyException;
import edu.kit.iti.algover.parser.DafnyParserException;
import edu.kit.iti.algover.proof.Proof;
import edu.kit.iti.algover.proof.ProofStatus;
import edu.kit.iti.algover.util.FormatException;
import edu.kit.iti.algover.util.TestUtil;
import org.junit.Assume;
import org.junit.Ignore;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;

import java.io.File;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

import static org.junit.Assert.assertEquals;


@RunWith(Parameterized.class)
public class PlayProofsTest {

    private static final String baseDir =
            System.getProperty("algover.cli.test-res", "test-res");

    private final AlgoVerService service;

    @Parameters(name= "{0}")
    public static Collection<Object[]> data() {
        System.err.println(new File(".").getAbsolutePath());

        List<Object[]> result = new ArrayList<>();

        File base = new File(baseDir.replace('/', File.separatorChar));

        for (File dir : base.listFiles()) {
            if (dir.isDirectory()) {
                for (File file : dir.listFiles()) {
                    if (file.getName().matches("config.*\\.xml")) {
                        result.add(new Object[]{dir, file.getName()});
                    }
                }
            }
        }

        return result;
    }

    public PlayProofsTest(File directory, String configFile) {
        service = new AlgoVerService(directory);
        service.setConfigName(configFile);
        service.setVerbosityLevel(TestUtil.VERBOSE ? 2 : 0);
    }

    @Test
    public void parse() throws FormatException, DafnyParserException, DafnyException, IOException {
        service.getProjectManager();
    }

    @Test
    // @Ignore // as long as the script replay are not there ... and no z3 ...
    public void run() throws FormatException, DafnyParserException, DafnyException, IOException {

        try {
            parse();
        } catch(Throwable ex) {
            Assume.assumeNoException("Parsing works fine", ex);
        }

        // File parseOnlyFile = new File(service.getDirectory(), "PARSE_ONLY");
        // Assume.assumeTrue(!parseOnlyFile.exists());

        List<Proof> proofs = service.runVerification();

        for (Proof proof : proofs) {
            if(proof.getFailException() != null) {
                proof.getFailException().printStackTrace();
            }
            assertEquals("Unclosed proof " + proof.getPVCName(), ProofStatus.CLOSED, proof.getProofStatus());
        }
    }


}
