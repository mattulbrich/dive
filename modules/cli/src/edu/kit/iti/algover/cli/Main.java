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
import edu.kit.iti.algover.parser.DafnyException;
import edu.kit.iti.algover.parser.DafnyParserException;
import edu.kit.iti.algover.project.ProjectManager;
import edu.kit.iti.algover.proof.PVC;
import edu.kit.iti.algover.proof.Proof;
import edu.kit.iti.algover.proof.ProofStatus;
import edu.kit.iti.algover.util.CommandLine;
import edu.kit.iti.algover.util.ExceptionDetails;
import edu.kit.iti.algover.util.FormatException;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.util.List;
import java.util.function.Predicate;

/**
 * This is the entry point of AlgoVer when used as a command line tool.
 *
 * Run the tool with "-help" or refer to {@link #prepareCommandLine()} to
 * find out about the command line options.
 *
 * @author Mattias Ulbrich
 */
public class Main {

    public static final String OPTION_CONFIG_FILENAME = "-c";
    public static final String OPTION_VERBOSE = "-verbose";
    public static final String OPTION_VERY_VERBOSE = "-vverbose";
    public static final String OPTION_METHOD = "-method";
    public static final String OPTION_CLASS = "-class";
    public static final String OPTION_PVC_MATCH = "-pvcMatch";
    public static final String OPTION_HELP = "-help";

    public static void main(String[] args) {
        CommandLine cl = prepareCommandLine();
        try {

            cl.parse(args);

            if (cl.isSet(OPTION_HELP)) {
                cl.printUsage(System.out);
                return;
            }

            if (cl.getArguments().isEmpty()) {
                throw new IllegalArgumentException("Please specify the directory/-ies which are to be checked");
            }

            boolean success = true;
            for (String arg : cl.getArguments()) {
                success &= processDirectory(arg, cl);
            }

            System.out.println("Build " + (success ? "SUCCEEDED" : "FAILED"));

            System.exit(success ? 0 : 1);

        } catch(Exception ex) {
            if(cl.isSet(OPTION_VERBOSE)) {
                ex.printStackTrace();
            }

            ExceptionDetails.printNiceErrorMessage(ex);
        }

    }

    private static boolean processDirectory(String dir, CommandLine cl) {

        String configFilename = cl.getString(OPTION_CONFIG_FILENAME, AlgoVerService.DEFAULT_CONFIG_FILENAME);

        String methodMatch = cl.getString(OPTION_METHOD, null);
        String classMatch = cl.getString(OPTION_CLASS, null);
        String pvcRegexMatch = cl.getString(OPTION_PVC_MATCH, ".*");
        Predicate<PVC> filter = pvc -> {
            DafnyDecl decl = pvc.getDeclaration();

            if(decl instanceof DafnyMethod) {
                if (methodMatch != null && !methodMatch.equals(decl.getName())) {
                    return false;
                }

                DafnyDecl parent = decl.getParentDecl();
                if (classMatch != null && parent instanceof DafnyClass && !classMatch.equals(parent.getName())) {
                    return false;
                }
            }

            return pvc.getIdentifier().matches(pvcRegexMatch);
        };

        boolean verbose = cl.isSet(OPTION_VERBOSE);

        int verbosity = 0;
        if (verbose) {
            verbosity = 1;
        }
        if (cl.isSet(OPTION_VERY_VERBOSE)) {
            verbosity = 2;
            verbose = true;
        }

        AlgoVerService service = new AlgoVerService(new File(dir));
        service.setConfigName(configFilename);
        service.setPVCFilter(filter);
        service.setVerbosityLevel(verbosity);

        try {

            boolean result = true;
            List<Proof> proofs = service.runVerification();
            for (Proof proof : proofs) {
                if (proof.getProofStatus() != ProofStatus.CLOSED) {
                    if (result) {
                        System.err.println("Unclosed proofs for " + dir);
                    }
                    System.err.println("  " + proof.getPVCName() + " : " + proof.getProofStatus());
                    result = false;
                }
            }
            return result;

        } catch (Exception ex) {

            System.err.println("Error while verifying " + dir + ":");
            if(verbose) {
                ex.printStackTrace();
            }
            ExceptionDetails.printNiceErrorMessage(ex);

            return false;
        }

    }

    private static CommandLine prepareCommandLine() {
        CommandLine result = new CommandLine();
        result.addOption(OPTION_CONFIG_FILENAME, "configFile",
                "Name of the configuration file, default: " +
                        AlgoVerService.DEFAULT_CONFIG_FILENAME);
        result.addOption(OPTION_METHOD, "methodName",
                "only check VCs for given method");
        result.addOption(OPTION_CLASS, "className",
                "only check VCs for given class");
        result.addOption(OPTION_PVC_MATCH, "regex",
                "only check VCs whose name matches the argument");
        result.addOption(OPTION_VERBOSE, null,
                "Be verbose in the output");
        result.addOption(OPTION_VERY_VERBOSE, null,
                "Be very verbose in the output");
        result.addOption(OPTION_HELP, null,
                "Show help");
        return result;
    }
}
