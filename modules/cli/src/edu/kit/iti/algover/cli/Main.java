/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 *
 */

package edu.kit.iti.algover.cli;

import edu.kit.iti.algover.dafnystructures.DafnyClass;
import edu.kit.iti.algover.dafnystructures.DafnyDecl;
import edu.kit.iti.algover.dafnystructures.DafnyMethod;
import edu.kit.iti.algover.project.ProjectManager;
import edu.kit.iti.algover.proof.PVC;
import edu.kit.iti.algover.proof.Proof;
import edu.kit.iti.algover.proof.ProofStatus;
import edu.kit.iti.algover.util.CommandLine;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.util.List;

public class Main {

    public static final String OPTION_CONFIG_FILENAME = "-c";
    public static final String DEFAULT_CONFIG_FILENAME = "config.xml";

    public static void main(String[] args) throws Exception {
        CommandLine cl = prepareCommandLine();

        cl.parse(args);

        if(cl.getArguments().isEmpty()) {
            throw new IllegalArgumentException("Please specify the directory/-ies which are to be checked");
        }

        for (String arg : cl.getArguments()) {
            processDirectory(arg, cl);
        }

    }

    private static void processDirectory(String dir, CommandLine cl) throws Exception {

        String configFilename = cl.getString(OPTION_CONFIG_FILENAME, DEFAULT_CONFIG_FILENAME);
        ProjectManager pm = new ProjectManager(new File(dir), configFilename);

        String methodMatch = cl.getString("-method", null);
        String classMatch = cl.getString("-class", null);

        List<PVC> allPVCs = pm.getPVCGroup().getContents();
        for (PVC pvc : allPVCs) {
            DafnyDecl decl = pvc.getDeclaration();

            if(decl instanceof DafnyMethod) {
                if(methodMatch != null && !methodMatch.equals(decl.getName())) {
                    continue;
                }
                DafnyDecl parent = decl.getParentDecl();
                if(classMatch != null && parent instanceof DafnyClass && !classMatch.equals(parent.getName())) {
                    continue;
                }
            }

            processPVC(cl, pm, pvc.getIdentifier());

        }

    }

    private static void processPVC(CommandLine cl, ProjectManager pm, String pvc) throws IOException {

        String defaultScript = cl.getString("-defScript", "z3;");

        Proof proof = pm.getProofForPVC(pvc);
        try {
            pm.findAndParseScriptFileForPVC(pvc);
        } catch(FileNotFoundException ex) {
            proof.setNewScriptTextAndParser(defaultScript);
        }

        try {
            proof.interpretScript();
            ProofStatus status = proof.getProofStatus();
            System.out.println(pvc + " : " + status);
        } catch(Exception ex) {
            System.err.println(pvc + " : EXCEPTION");
            ex.printStackTrace();
        }

    }

    private static CommandLine prepareCommandLine() {
        CommandLine result = new CommandLine();
        result.addOption(OPTION_CONFIG_FILENAME, "configFile", "Name of the configuration file, default: " + DEFAULT_CONFIG_FILENAME);
        result.addOption("-method", "methodName", "only check VCs for given method");
        result.addOption("-class", "className", "only check VCs for given class");
        result.addOption("-pvcMatch", "regex", "only check VCs whose name matches the argument");
        result.addOption("-defScript", "script", "default script if none is stored in the files");
        return result;
    }
}
