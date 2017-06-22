/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover;

import edu.kit.iti.algover.dafnystructures.DafnyClass;
import edu.kit.iti.algover.dafnystructures.DafnyMethod;
import edu.kit.iti.algover.parser.DafnyException;
import edu.kit.iti.algover.parser.DafnyParser;
import edu.kit.iti.algover.parser.DafnyTree;
import edu.kit.iti.algover.project.Project;
import edu.kit.iti.algover.project.ProjectBuilder;
import edu.kit.iti.algover.proof.PVCGroup;
import edu.kit.iti.algover.proof.SinglePVC;
import edu.kit.iti.algover.util.Debug;
import edu.kit.iti.algover.util.Util;
import org.antlr.runtime.RecognitionException;

import java.io.File;

public class ProjectMain {

    public static void main(String[] args) {
        try {
            test(args);
        } catch (DafnyException e) {
            e.printStackTrace();

            System.err.println(e.getTree().toStringTree());
        } catch (RecognitionException e) {
            DafnyParser p = new DafnyParser(null);
            System.err.println( "line "+e.line+":"+e.charPositionInLine);
            System.err.println(p.getErrorMessage(e, p.getTokenNames()));
        } catch (Exception e) {
            e.printStackTrace();
        }

    }

    private static void test(String[] args) throws Exception {
        String dir = "modules/core/test-res/edu/kit/iti/algover/script".
                replace('/', File.separatorChar);

        ProjectBuilder pb = new ProjectBuilder();
        pb.setDir(new File(dir));
        pb.setConfigFilename("config.xml");  // is already default.

        pb.parseProjectConfigurationFile();  // if the script should be parsed.

        // to add extra files / libraries
        pb.addDafnyFile("extra.dfy");
        pb.addLibraryFile("lib.dfy");

        // to add other preparsed files to the project.
        pb.addDafnyTree("internal.dfy", new DafnyTree(DafnyParser.COMPILATION_UNIT));

        Project project = pb.build();

        /*
         * Accessing all declared symbols
         */
        System.out.println(Util.join(project.getAllDeclaredSymbols(), "\n"));

        /*
         * Finding one class.
         */
        DafnyClass clazz = project.getClass("Extra");
        assert !clazz.isInLibrary();

        DafnyClass lib = project.getClass("Lib");
        assert lib.isInLibrary();

        /*
         * Finding method
         */
        DafnyMethod method = project.getMethod("m2");
        System.out.println(Debug.prettyPrint(method.getRepresentation().toStringTree()));

        /*
         * All pvcs in a tree
         */
        PVCGroup pvcs = project.getAllVerificationConditions();
        System.out.println(Debug.toString(pvcs));

        /*
         * turn that into logic ... WORK IN PROGRESS
         */

        SinglePVC pv = (SinglePVC) project.getVerificationConditionsFor(project.getMethod("m2")).getChildren().get(1);
        System.out.println(pv.getPVC().getSequent().getAntecedent());

        // @Sarah: How do I get the actual pvc from a collection?
        // PVC pvc = pvcs.getChild(1).getChildren().get(2);

    }

}
