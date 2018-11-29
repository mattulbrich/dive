/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.proof;


import java.util.ArrayList;
import java.util.Map;

import edu.kit.iti.algover.dafnystructures.DafnyClass;
import edu.kit.iti.algover.dafnystructures.DafnyDecl;
import edu.kit.iti.algover.data.BuiltinSymbols;
import edu.kit.iti.algover.data.MapSymbolTable;
import edu.kit.iti.algover.data.SymbolTable;
import edu.kit.iti.algover.parser.DafnyTree;
import edu.kit.iti.algover.project.Project;
import edu.kit.iti.algover.rules.TermSelector;
import edu.kit.iti.algover.symbex.SymbexPath;
import edu.kit.iti.algover.term.Sequent;
import nonnull.NonNull;
import nonnull.Nullable;

/**
 *
 * Class capturing <b>P</b>roof <b>V</b>erification <b>C</b>onditions.
 *
 * <p>
 * A PVC may correspond to a {@link SymbexPath} for methods or a proof
 * obligation for functions.
 *
 * <p>
 * PVC is an immutable class.
 *
 * @author Created by sarah on 8/22/16.
 * @author refined by mattias 8/27/17.
 *
 * @see MethodPVCBuilder
 */
public class PVC {

    /**
     * Path through program.
     *
     * May be <code>null</code> if the source is a function and not method.
     * Invariant:
     * {@code pathThroughProgram == null ==> declaration instanceof DafnyMethod}.
     */
    private final @Nullable SymbexPath pathThroughProgram;

    /**
     * DafnDecl this PVC belongs to. not <code>null</code>
     */
    private final @NonNull DafnyDecl declaration;

    /**
     * The sequent which serves as the root node in the proof tree.
     */
    private final @NonNull Sequent sequent;

    /**
     * A map which assigns all relevant term selectors to {@link #sequent}
     * to the respective {@link DafnyTree}s from the sources.
     */
    private final @NonNull Map<TermSelector, DafnyTree> referenceMap;

    /**
     * The symbol table containing all base symbols (in contrast to added symbols while applying rules) which
     * occur in the {@link #sequent}.
     */
    private final @NonNull SymbolTable baseSymbolTable;

    /**
     * Reference to the project to which this PVC belongs.
     */
    private final Project project;

    /**
     * The identifier of this PVC.
     *
     * In case of method invocations its the identifier of the path.
     */
    private final String identifier;

    /**
     * Instantiates a new PVC. The informations are taken from a builder object.
     *
     * @param builder the builder to take relevant info from, not <code>null</code>.
     * @see MethodPVCBuilder#build()
     */
    public PVC(PVCBuilder builder) {
        this.project = builder.getProject();
        this.pathThroughProgram = builder.getPathThroughProgram();
        this.declaration = builder.getDeclaration();
        this.sequent = builder.getSequent();
        this.baseSymbolTable = builder.getSymbolTable();
        this.identifier = getDeclarationPrefix()
                + "/" + builder.getPathIdentifier();
        this.referenceMap = builder.getReferenceMap();
    }

    private String getDeclarationPrefix() {

        if (declaration == null) {
            // can appear in test cases
            return "(null)";
        }

        DafnyDecl clss = declaration.getParentDecl();
        if(clss instanceof DafnyClass) {
            return clss.getName() + "." + declaration.getName();
        } else {
            return declaration.getName();
        }
    }

    @Override
    public String toString() {
        return "PVC[" + getIdentifier() + "]";
    }

    public SymbexPath getPathThroughProgram() {
        return pathThroughProgram;
    }

    public DafnyDecl getDeclaration() {
        return declaration;
    }

    public Sequent getSequent() {
        return sequent;
    }

    public SymbolTable getSymbolTable() {
        return baseSymbolTable;
    }

    public String getIdentifier() {
        return identifier;
    }

    public Map<TermSelector, DafnyTree> getReferenceMap() {
        return referenceMap;
    }

    public Project getProject() {
        return project;
    }
}
