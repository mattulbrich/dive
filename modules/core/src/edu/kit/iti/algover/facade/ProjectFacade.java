/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.facade;

import edu.kit.iti.algover.dafnystructures.DafnyDecl;
import edu.kit.iti.algover.parser.DafnyException;
import edu.kit.iti.algover.parser.ReferenceResolutionVisitor;
import edu.kit.iti.algover.parser.TypeResolution;
import edu.kit.iti.algover.project.Project;
import edu.kit.iti.algover.project.ProjectBuilder;
import edu.kit.iti.algover.proof.PVC;
import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.symbex.Symbex;
import edu.kit.iti.algover.symbex.SymbexPath;
import edu.kit.iti.algover.theoremprover.DafnyTranslator;

import java.io.File;
import java.io.FileNotFoundException;
import java.util.ArrayList;
import java.util.List;

/**
 * Interface to create a project, to reload a project and do other project related stuff
 * Created by sarah on 8/22/16.
 */
//Use ProjectManager instead
@Deprecated
public class ProjectFacade {

    /**
     * Class is singleton
     */
    private static ProjectFacade instance = null;
    /**
     * General Counter for PVCs
     */
    private int generalPVCCounter;

    protected ProjectFacade() {
        generalPVCCounter = 0;
    }

    public static ProjectFacade getInstance() {
      if(instance == null) {
         instance = new ProjectFacade();
      }
      return instance;
    }

    /**
     * Build a new Project
     * @param dir
     * @return
     * //TODO Create Parsing Exception for config file
     */
    // REVIEW Duplicated method: in ProjectManager and ProjectFacade.
    public static Project buildProject(File dir) throws FileNotFoundException, Exception {
        Project p = null;
        ProjectBuilder pb = new ProjectBuilder();
        pb.setDir(dir);
        pb.parseProjectConfigurationFile();
        pb.validateProjectConfiguration();
        p = pb.build();

        ArrayList<DafnyException> exceptions = new ArrayList<>();
        ReferenceResolutionVisitor refResolver = new ReferenceResolutionVisitor(p, exceptions);
        refResolver.visitProject();

        TypeResolution typeRes = new TypeResolution(exceptions);
        typeRes.visitProject(p);

        return p;
    }



    /**
     * Perform Symbolic Execution of a given DafnyTree (method)
     * @param decl  DafnyDecl representing a method
     * @return
     */
    public static List<SymbexPath> performSymbolicExecution(DafnyDecl decl) {

        Symbex symbex = new Symbex();
        List<SymbexPath> result = symbex.symbolicExecution(decl.getRepresentation());
        return result;
    }

    public static ProofNode createProofRoot(SymbexPath path) {
        return null;
    }

    public static void translateToDafny(PVC verificationCondition) {
        DafnyTranslator trans = new DafnyTranslator(verificationCondition, 1);
        //return file to which it will be translated
    }

   /* public static ScriptTree getScriptFor(int pvcId) {
        return null;
    }*/

    private int getGeneralPVCCounter() {
        return generalPVCCounter;
    }

    private void setGeneralPVCCounter(int generalPVCCounter) {
        this.generalPVCCounter += generalPVCCounter;
    }
}
