/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.proof;

import java.lang.IllegalStateException;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.Map;

import edu.kit.iti.algover.ProgramDatabase;
import edu.kit.iti.algover.dafnystructures.DafnyDecl;
import edu.kit.iti.algover.dafnystructures.DafnyMethod;
import edu.kit.iti.algover.data.BuiltinSymbols;
import edu.kit.iti.algover.data.MapSymbolTable;
import edu.kit.iti.algover.data.SuffixSymbolTable;
import edu.kit.iti.algover.data.SymbolTable;
import edu.kit.iti.algover.parser.DafnyException;
import edu.kit.iti.algover.parser.DafnyParser;
import edu.kit.iti.algover.parser.DafnyTree;
import edu.kit.iti.algover.project.Project;
import edu.kit.iti.algover.rules.TermSelector;
import edu.kit.iti.algover.settings.ProjectSettings;
import edu.kit.iti.algover.symbex.LocalVarDecl;
import edu.kit.iti.algover.symbex.SymbexPath;
import edu.kit.iti.algover.term.FunctionSymbol;
import edu.kit.iti.algover.term.Sequent;
import edu.kit.iti.algover.term.Sort;
import edu.kit.iti.algover.term.builder.PVCSequenter;
import edu.kit.iti.algover.term.builder.TermBuildException;
import edu.kit.iti.algover.util.ASTUtil;
import edu.kit.iti.algover.util.ExceptionDetails;
import edu.kit.iti.algover.util.TreeUtil;

/**
 * Builder for {@link PVC} from a {@link DafnyMethod} and a {@link SymbexPath}.
 *
 * This class is not ready for multi-threading.
 *
 * @author Created by sarah on 8/18/16.
 * @author Revised by mattias on 8/27/17.
 * @see PVC
 */
public class MethodPVCBuilder implements PVCBuilder {

    private final Project project;
    /**
     * Path through program which represents state of this pvc
     */
    private SymbexPath pathThroughProgram;

    /**
     * The procedure that produces the {@link Sequent} for this builder.
     */
    private PVCSequenter sequenter;

    /**
     * DafnyMethod to which this PVC belongs
     */
    private DafnyDecl declaration;

    private SymbolTable symbolTable;

    private Sequent sequent;

    private Map<TermSelector, DafnyTree> referenceMap;

    public MethodPVCBuilder(Project project) {
        this.project = project;
        if(project != null) {
            this.sequenter = findSequenter(project.getSettings().getString(ProjectSettings.SEQUENTER));
        }
    }

    public static PVCSequenter findSequenter(String string) {
        for (PVCSequenter instance : PVCSequenter.INSTANCES) {
            if(instance.getName().equals(string))
                return instance;
        }
        // This should not happen since settings can be validated
        throw new IllegalStateException("Unknown sequenter: " + string);
    }

    public PVC build() throws TermBuildException {
        return new PVC(this);
    }

    public SymbexPath getPathThroughProgram() {
        return pathThroughProgram;
    }

    public MethodPVCBuilder setPathThroughProgram(SymbexPath pathThroughProgram) {
        this.sequent = null;
        this.pathThroughProgram = pathThroughProgram;
        return this;
    }

    public DafnyDecl getDeclaration() {
        return declaration;
    }

    public MethodPVCBuilder setDeclaration(DafnyDecl decl) {
        this.sequent = null;
        this.declaration = decl;
        return this;
    }

    public SymbolTable getSymbolTable() {
        if(symbolTable == null) {
            symbolTable = makeSymbolTable();
        }
        return symbolTable;
    }

    private SymbolTable makeSymbolTable() {

        Collection<FunctionSymbol> map = new ArrayList<>();

        DafnyDecl method = declaration;

        for (DafnyTree decl : ProgramDatabase.getAllVariableDeclarations(method.getRepresentation())) {
            String name = decl.getChild(0).toString();
            Sort sort = ASTUtil.toSort(decl.getFirstChildWithType(DafnyParser.TYPE).getChild(0));
            map.add(new FunctionSymbol(name, sort));
        }

        for (LocalVarDecl lvd : pathThroughProgram.getDeclaredLocalVars()) {
            String name = lvd.getName();
            Sort sort = TreeUtil.toSort(lvd.getType());
            map.add(new FunctionSymbol(name, sort));
        }

        // TODO is this suffix stuff still needed?
        // MapSymbolTable st = new SuffixSymbolTable(new BuiltinSymbols(), map);
        MapSymbolTable st = new MapSymbolTable(new BuiltinSymbols(), map);

        project.getAllDeclaredSymbols().forEach(st::addFunctionSymbol);

        return st;
    }

    public void ensureSequentExists() {
        if(sequent == null) {
            try {
                this.referenceMap = new HashMap<TermSelector, DafnyTree>();
                this.sequent =
                        sequenter.translate(pathThroughProgram, getSymbolTable(), referenceMap);
            } catch (DafnyException e) {
                ExceptionDetails.printNiceErrorMessage(e);
                // FIXME TODO Auto-generated catch block
                throw new Error(e);
            }
        }
    }

    public Sequent getSequent() {
        ensureSequentExists();
        return sequent;
    }

    public Map<TermSelector, DafnyTree> getReferenceMap() {
        ensureSequentExists();
        return Collections.unmodifiableMap(referenceMap);
    }

    @Override
    public String getPathIdentifier() {
        return pathThroughProgram.getPathIdentifier();
    }

    @Override
    public Project getProject() {
        return project;
    }

    public PVCSequenter getSequenter() {
        return sequenter;
    }

    public void setSequenter(PVCSequenter sequenter) {
        this.sequent = null;
        this.sequenter = sequenter;
    }

}
