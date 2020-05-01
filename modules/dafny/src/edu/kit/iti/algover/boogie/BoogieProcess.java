/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.boogie;

import edu.kit.iti.algover.data.SymbolTable;
import edu.kit.iti.algover.project.Project;
import edu.kit.iti.algover.rules.RuleException;
import edu.kit.iti.algover.term.Sequent;
import edu.kit.iti.algover.term.builder.TermBuildException;
import nonnull.NonNull;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.nio.file.Files;
import java.nio.file.Path;
import java.security.NoSuchAlgorithmException;
import java.util.Arrays;
import java.util.Map;

/**
 * This class controls the communication to a boogie process.
 *
 * For every query a new process is launched.
 *
 * @author Mattias Ulbrich
 */
public class BoogieProcess {

    /**
     * The command by which Boogie is invoked.
     */
    public static final String COMMAND =
            System.getProperty("edu.kit.iti.algover.boogie_binary", "boogie");

    /**
     * If true, all produced temporary .bpl files are kept.
     */
    public static final boolean KEEP_BPL =
            Boolean.getBoolean("edu.kit.iti.algover.keepBPL");

    /**
     * If true, all produced temporary .bpl files are kept.
     */
    public static final boolean VERBOSE_BOOGIE =
            Boolean.getBoolean("edu.kit.iti.algover.verboseBPL");

    /**
     * The class responsible for the translation
     */
    private final BoogieTranslation translation;


    /**
     * Instantiate a new boogie connection for a project
     *
     * @param project the project for which to translate a sequent.
     * @param table the table containing all symbols occurring on the sequent
     * @param sequent the logical encoding of the problem to solve
     */
    public BoogieProcess(@NonNull Project project, SymbolTable table, Sequent sequent) {
        this.translation = new BoogieTranslation(project);
        this.translation.setSequent(sequent);
        this.translation.setSymbolTable(table);
    }

    /**
     * Some applications may require additional text that is sent to Boogie.
     * Especially for testing.
     */
    private String additionalBoogieText = "";

    /**
     *
     * @return whether or not boogie was able to close the target
     * @throws RuleException if boogie somehow ran into problems
     */
    public boolean callBoogie() throws TermBuildException, IOException, RuleException {

        CharSequence sb = translation.getObligation();

        // The boogie code is stored in a temporary file
        Path tmpFile = Files.createTempFile("dive-", ".bpl");

        // which is deleted unless required
        if(!KEEP_BPL) {
            tmpFile.toFile().deleteOnExit();
        }

        // write prelude, obligation and add. code
        Files.write(tmpFile, Arrays.asList(BoogieTranslation.PRELUDE, sb, additionalBoogieText));

        Process process = buildProcess(tmpFile);
        InputStream in = process.getInputStream();

        // read lines from process and look for error indications
        BufferedReader br = new BufferedReader(new InputStreamReader(in));
        String line;
        while ((line = br.readLine()) != null) {
            if(VERBOSE_BOOGIE){
                System.out.println(" Boogie > " + line);
            }
            if (line.matches("Boogie program verifier finished with \\d+ verified, 0 errors"))
                return true;
            if (line.startsWith("Boogie program verifier finished with"))
                return false;
        }

        throw new RuleException("Oh dear, boogie seems to fail for " + tmpFile);
    }

    private Process buildProcess(Path tmpFile) throws IOException {
        ProcessBuilder pb;
        if(System.getProperty("os.name").toLowerCase().contains("windows")) {
            pb = new ProcessBuilder("cmd", "/c", COMMAND + " " + tmpFile.toString());
            String path = System.getenv("PATH");
            Map<String, String> env = pb.environment();
            env.put("PATH", path);
            if(VERBOSE_BOOGIE){
                System.out.println(" Boogie called via '" + "cmd /c " + COMMAND + " " + tmpFile.toString());
            }
        } else {
            pb = new ProcessBuilder(COMMAND, tmpFile.toString());
            if(VERBOSE_BOOGIE){
                System.out.println(" Boogie called via '" + COMMAND + " " + tmpFile + "'");
            }
        }

        return pb.start();
    }

    /**
     * Set extra text in Boogie.
     *
     * Some applications may require additional text that is sent to Boogie.
     * Especially for testing.
     * @param additionalBoogieText non-null text to append to the BPL output.
     */

    public void setAdditionalBoogieText(@NonNull String additionalBoogieText) {
        this.additionalBoogieText = additionalBoogieText;
    }

    /**
     * Retrieve the proof obligation of this object.
     *
     * @return the boogie proof obligation handled by this object
     * @throws NoSuchAlgorithmException never actually (I hope)
     * @throws TermBuildException if obligation creation is broken
     */
    public CharSequence getObligation() throws TermBuildException {
        return translation.getObligation();
    }

    /**
     * Retrieve a hash code for the proof obligation
     *
     * @return the hash code of the proof obligation handled by this object
     * @throws NoSuchAlgorithmException never actually (I hope)
     * @throws TermBuildException if obligation creation is broken
     */
    public String getHash() throws NoSuchAlgorithmException, TermBuildException {
        return translation.getHash();
    }
}
