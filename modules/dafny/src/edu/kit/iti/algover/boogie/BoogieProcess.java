/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.boogie;

import edu.kit.iti.algover.data.SymbolTable;
import edu.kit.iti.algover.project.Project;
import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.rules.RuleException;
import edu.kit.iti.algover.rules.impl.BoogieCache;
import edu.kit.iti.algover.term.builder.TermBuildException;
import edu.kit.iti.algover.util.Util;
import nonnull.NonNull;

import java.io.IOException;
import java.io.InputStream;
import java.nio.file.Files;
import java.nio.file.Path;
import java.security.NoSuchAlgorithmException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.LinkedHashSet;
import java.util.List;
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
    public static final boolean KEEP_BPL = true;
//            Boolean.getBoolean("edu.kit.iti.algover.keepBPL");

    /**
     * If true, all produced temporary .bpl files are kept.
     */
    public static final boolean VERBOSE_BOOGIE = true;
//            Boolean.getBoolean("edu.kit.iti.algover.verboseBPL");

    /**
     * The collection of sequent translations
     */
    private final List<BoogieTranslation> translations;

    /**
     * Instantiate a new boogie connection for a single sequent.
     *
     * @param project the project for which to translate a sequent.
     * @param table the table containing all symbols occurring on the sequent
     * @param proofNode the proof node of the problem to solve
     */
    public BoogieProcess(@NonNull Project project, SymbolTable table, ProofNode proofNode) {
        this(project, table, List.of(proofNode));
    }

    /**
     * Instantiate a new boogie connection for a list of sequents.
     *
     * @param project the project for which to translate a sequent.
     * @param table the table containing all symbols occurring on the sequent
     * @param proofNodes the list of proof nodes of the problem to solve
     */
    public BoogieProcess(@NonNull Project project, SymbolTable table, List<ProofNode> proofNodes) {
        this.translations = new ArrayList<>();
        int suffix = 0;
        boolean multiProcess = proofNodes.size() > 1;
        for (ProofNode pnode : proofNodes) {
            BoogieTranslation translation = new BoogieTranslation(project);
            translation.setProofNode(pnode);
            translation.setSymbolTable(table);
            if (multiProcess) {
                translation.setSuffix(suffix);
                suffix++;
            }
            translations.add(translation);
        }
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
    public boolean callBoogie() throws TermBuildException, IOException, RuleException, NoSuchAlgorithmException {

        String boogieCode = getBoogieCode();

        // The boogie code is stored in a temporary file
        Path tmpFile = Files.createTempFile("dive-", ".bpl");

        // which is deleted unless required
        if(KEEP_BPL) {
            System.err.println("Boogie output under: " + tmpFile);
        } else {
            tmpFile.toFile().deleteOnExit();
        }

        // write prelude, obligation and add. code
        Files.write(tmpFile, Arrays.asList(BoogieTranslation.PRELUDE, boogieCode, additionalBoogieText));

        Process process = buildProcess(tmpFile);
        InputStream in = process.getInputStream();

        BoogieResponseParser boogieResponseParser = new BoogieResponseParser(boogieCode);
        boogieResponseParser.readFrom(in);
        if (boogieResponseParser.isConsistent()) {
            // write back solutions to the objects
            for (Integer p : boogieResponseParser.getVerifiedProcedures()) {
                BoogieTranslation translation = translations.get(p);
                BoogieCache.add(translation.getHash());
                translation.setVerified(true);
            }
            return boogieResponseParser.getFailedProcedures().isEmpty();
        } else {
            throw new RuleException("Oh dear, boogie seems to fail for " + tmpFile);
        }
    }

    /* can be used in testing, too. Hence, package visible */
    static Process buildProcess(Path tmpFile) throws IOException {
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
     * Mainly for testing.
     *
     * @return the boogie proof obligation handled by this object
     * @throws TermBuildException if obligation creation is broken
     */
    public String getBoogieCode() throws TermBuildException {
        Collection<String> elements = new ArrayList<>();
        for (BoogieTranslation translation : translations) {
            elements.addAll(translation.getObligation());
        }
        String boogieCode = Util.join(elements, "\n");
        return boogieCode;
    }

    /**
     * Retrieve a hash code for the proof obligation.
     *
     * This is only available if the process wraps a single sequent!
     *
     * @return the hash code of the proof obligation handled by this object
     * @throws NoSuchAlgorithmException never actually (I hope)
     * @throws TermBuildException if obligation creation is broken
     */
    public String getHash() throws NoSuchAlgorithmException, TermBuildException {
        if (translations.size() != 1) {
            throw new IllegalStateException("internal error: hashes can only obtained for single translations");
        }
        return translations.get(0).getHash();
    }
}
