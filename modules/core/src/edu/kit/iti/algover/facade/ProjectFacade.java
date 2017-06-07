/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.facade;

import java.io.File;
import java.io.FileNotFoundException;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

import edu.kit.iti.algover.dafnystructures.DafnyDecl;
import edu.kit.iti.algover.dafnystructures.DafnyDeclPVCCollector;
import edu.kit.iti.algover.dafnystructures.DafnyFile;
import edu.kit.iti.algover.parser.DafnyException;
import edu.kit.iti.algover.parser.ReferenceResolutionVisitor;
import edu.kit.iti.algover.parser.TypeResolution;
import edu.kit.iti.algover.project.Project;
import edu.kit.iti.algover.project.ProjectBuilder;
import edu.kit.iti.algover.proof.PVC;
import edu.kit.iti.algover.proof.PVCGroup;
import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.script.ScriptTree;
import edu.kit.iti.algover.symbex.Symbex;
import edu.kit.iti.algover.symbex.SymbexPath;
import edu.kit.iti.algover.term.FunctionSymbol;
import edu.kit.iti.algover.theoremprover.DafnyTranslator;

/**
 * Interface to create a project, to reload a project and do other project related stuff
 * Created by sarah on 8/22/16.
 */

// REVIEW: Perhaps this should really be a collection of static functions.
// The singleton pattern does not seem to be really followed everywhere.

public class ProjectFacade {

    private int getGeneralPVCCounter() {
        return generalPVCCounter;
    }

    private void setGeneralPVCCounter(int generalPVCCounter) {
        this.generalPVCCounter += generalPVCCounter;
    }

    /**
     * General Counter for PVCs
     */
    private int generalPVCCounter;

    /**
     * Class is singleton
     */
    private static ProjectFacade instance = null;
    protected ProjectFacade() {
        generalPVCCounter = 0;
    }

    public static ProjectFacade getInstance() {
      if(instance == null) {
         instance = new ProjectFacade();
      }
      return instance;
    }

    // REVIEW: "throws Exception" is usually not a very good idea.
    /**
     * Build a new Project
     * @param dir
     * @return
     */
    public Project buildProject(File dir) throws FileNotFoundException, Exception {
        Project p = null;
        ProjectBuilder pb = new ProjectBuilder();
        pb.setDir(dir);
        pb.parseScript();
        p = pb.build();

        ArrayList<DafnyException> exceptions = new ArrayList<>();
        ReferenceResolutionVisitor refResolver = new ReferenceResolutionVisitor(p, exceptions);
        refResolver.visitProject();

        TypeResolution typeRes = new TypeResolution(exceptions);
        typeRes.visitProject(p);

        return p;
    }

    /**
     * Performs Symbolic execution of a dafnydecl and return the list of PVCs
     * @param decl
     * @return
     */
    // REVIEW: Why not as member function of project?
    public PVCGroup generateAndCollectPVC(Project project){

        PVCGroup root = new PVCGroup(null);

        DafnyDeclPVCCollector visitor = new DafnyDeclPVCCollector(ProjectFacade.getInstance());

        for (DafnyFile file : project.getDafnyFiles()) {
            visitor.visitFile(file, root);
        }

        return root;

    }

    /**
     * Perform Symbolic Execution of a given DafnyTree (method)
     * @param decl  DafnyDecl representing a method
     * @return
     */
    public List<SymbexPath> performSymbolicExecution(DafnyDecl decl){

        Symbex symbex = new Symbex();
        List<SymbexPath> result = symbex.symbolicExecution(decl.getRepresentation());
        return result;


    }

    // REVIEW: retired this. OK? Please remove if so.
    // all PVCs are recoverable from generateAndCollectPVC.
//    /**
//     * Create verification conditions from given SymbexPaths
//     * @param path SymbexPath
//     * @return
//     */
//    public List<PVC> createVerificationConditions(DafnyDecl decl, SymbexPath path) {
//        List<PVC> verificationconditions = new LinkedList<>();
//        PVCBuilder builder = new PVCBuilder(this.getGeneralPVCCounter());
//
//        //build all pvc for path
//        //in a loop
//        verificationconditions.add(builder.buildPVC(path, decl));
//
//
//        //add pvcs to counter
//        this.setGeneralPVCCounter(verificationconditions.size());
//        return verificationconditions;
//    }

    public ProofNode createProofRoot(SymbexPath path){
        return null;
    }

    public void translateToDafny(PVC verificationCondition){
        DafnyTranslator trans = new DafnyTranslator(verificationCondition, 1);
        //return file to which it will be translated
    }

    public ScriptTree getScriptFor(int pvcId){
        return null;
    }
}
