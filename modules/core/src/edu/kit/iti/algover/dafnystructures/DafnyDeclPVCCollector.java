/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.dafnystructures;


import java.util.HashSet;
import java.util.List;
import java.util.Set;

import edu.kit.iti.algover.project.Project;
import edu.kit.iti.algover.proof.MethodPVCBuilder;
import edu.kit.iti.algover.proof.PVC;
import edu.kit.iti.algover.proof.PVCCollection;
import edu.kit.iti.algover.proof.PVCGroup;
import edu.kit.iti.algover.proof.SinglePVC;
import edu.kit.iti.algover.symbex.FunctionObligationMaker;
import edu.kit.iti.algover.symbex.Symbex;
import edu.kit.iti.algover.symbex.SymbexPath;
import edu.kit.iti.algover.term.builder.TermBuildException;

/**
 * Visitor for DafnyDecl, that performs symbex on dafnydecl and returns PVCCollection
 * Created by sarah on 10/20/16.
 * refactored by mattias
 * @author Sarah Grebing
 */
public class DafnyDeclPVCCollector {


    private Project project;

    public DafnyDeclPVCCollector(Project project) {
        this.project = project;
    }

    public PVCCollection visitClass(DafnyClass cl) {
        PVCGroup clGroup = new PVCGroup(cl);

        for(DafnyFunction f :cl.getFunctions()) {
            clGroup.addChild(visitFunction(f));
        }

        for(DafnyMethod m :cl.getMethods()) {
            clGroup.addChild(visitMethod(m));
        }

        return clGroup;
    }

    public PVCCollection visitMethod(DafnyMethod m) {
        Set<String> seenNames = new HashSet<>();
        PVCGroup mGroup = new PVCGroup(m);

        Symbex symbex = new Symbex();
        List<SymbexPath> paths = symbex.symbolicExecution(m.getRepresentation());
        for (SymbexPath path : paths) {
            List<SymbexPath> subpaths = path.split();
            for (SymbexPath subpath : subpaths) {
                giveUniqueIdentifier(subpath, seenNames);
                MethodPVCBuilder builder = new MethodPVCBuilder(project);
                builder
                    .setPathThroughProgram(subpath)
                    .setDeclaration(m);

                PVC pvc = builder.build();
                SinglePVC sPVC = new SinglePVC(pvc);
                mGroup.addChild(sPVC);
            }
        }

        return mGroup;
    }

    private void giveUniqueIdentifier(SymbexPath path, Set<String> seenNames) {
        while(seenNames.contains(path.getPathIdentifier())) {
            path.incrementVariant();
        }
        seenNames.add(path.getPathIdentifier());
    }

    public PVCCollection visitFunction(DafnyFunction f) {
        Set<String> seenNames = new HashSet<>();
        PVCGroup mGroup = new PVCGroup(f);

        FunctionObligationMaker obligationMaker = new FunctionObligationMaker();
        List<SymbexPath> paths = obligationMaker.visit(f.getRepresentation());
        for (SymbexPath path : paths) {
            List<SymbexPath> subpaths = path.split();
            for (SymbexPath subpath : subpaths) {
                giveUniqueIdentifier(subpath, seenNames);
                MethodPVCBuilder builder = new MethodPVCBuilder(project);
                builder
                        .setPathThroughProgram(subpath)
                        .setDeclaration(f);
                PVC pvc;
                pvc = builder.build();
                SinglePVC sPVC = new SinglePVC(pvc);
                mGroup.addChild(sPVC);
            }
        }
        return mGroup;
    }

    // no collection per file!
    public void visitFile(DafnyFile file, PVCGroup collection) {

        if(file.isInLibrary()) {
            // Only input resources create PVCs
            return;
        }

        for (DafnyFunction f : file.getFunctions()) {
            collection.addChild(visitFunction(f));
        }

        for(DafnyMethod m : file.getMethods()) {
            collection.addChild(visitMethod(m));
        }

        for(DafnyClass c : file.getClasses()) {
            collection.addChild(visitClass(c));
        }
    }


}
