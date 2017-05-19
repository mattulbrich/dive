/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.facade;

import edu.kit.iti.algover.dafnystructures.DafnyClass;
import edu.kit.iti.algover.dafnystructures.DafnyDecl;
import edu.kit.iti.algover.dafnystructures.DafnyFunction;
import edu.kit.iti.algover.dafnystructures.DafnyMethod;
import edu.kit.iti.algover.parser.DafnyException;
import edu.kit.iti.algover.parser.ReferenceResolutionVisitor;
import edu.kit.iti.algover.parser.TypeResolution;
import edu.kit.iti.algover.project.*;
import edu.kit.iti.algover.proof.PVC;
import edu.kit.iti.algover.proof.PVCBuilder;
import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.script.ScriptTree;
import edu.kit.iti.algover.symbex.Symbex;
import edu.kit.iti.algover.symbex.SymbexPath;
import edu.kit.iti.algover.theoremprover.DafnyTranslator;

import java.io.File;
import java.io.FileNotFoundException;
import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;

/**
 * Interface to create a project, to reload a project and do other project related stuff
 * Created by sarah on 8/22/16.
 */
public class ProjectFacade {

    public int getGeneralPVCCounter() {
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

        p = pb.buildProject(dir);

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
    public List<PVC> generateAndCollectPVC(DafnyDecl decl){
        List<SymbexPath> paths = performSymbolicExecution(decl);
        List<PVC> pvcs = new ArrayList<>();
        for(SymbexPath path : paths){
            pvcs.addAll(createVerificationConditions(decl,path));
        }

        return pvcs;
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

    /**
     * Create verification conditions from given SymbexPaths
     * @param path SymbexPath
     * @return
     */
    public List<PVC> createVerificationConditions(DafnyDecl decl, SymbexPath path) {
        List<PVC> verificationconditions = new LinkedList<>();
        PVCBuilder builder = new PVCBuilder(this.getGeneralPVCCounter());

        //build all pvc for path
        //in a loop
        verificationconditions.add(builder.buildPVC(path, decl));


        //add pvcs to counter
        this.setGeneralPVCCounter(verificationconditions.size());
        return verificationconditions;
    }

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
