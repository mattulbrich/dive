/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.dafnystructures;

import java.util.ArrayList;
import java.util.List;

import edu.kit.iti.algover.parser.DafnyParser;
import edu.kit.iti.algover.parser.DafnyTree;

/**
 * A builder for Dafny functions.
 *
 * @see DafnyFunction
 */
public class DafnyFunctionBuilder {

    /**
     * The AST for this function.
     */
    private DafnyTree representation;

    /**
     * The filename of the file.
     */
    private String filename;

    /**
     * The name of the function.
     */
    private String name;

    /**
     * The list of function parameters.
     */
    private List<DafnyTree> params = new ArrayList<>();

    /**
     * The return type of the function.
     */
    private DafnyTree returnType;

    /**
     * The collection of requires clauses, not <code>null</code>.
     */
    private List<DafnyTree> requiresClauses = new ArrayList<>();

    /**
     * The collection of ensures clauses, not <code>null</code>.
     */
    private List<DafnyTree> ensuresClauses = new ArrayList<>();

    /**
     * The decreases clause if present.
     */
    private DafnyTree decreasesClause;

    /**
     * The expression of the function body. Must be defined.
     */
    private DafnyTree expression;

    /**
     * The flag for libraries.
     */
    private boolean inLibrary;

    /**
     * Instantiates a new dafny function builder.
     *
     * All lists are initialised.
     */
    public DafnyFunctionBuilder() {
    }

    public DafnyTree getRepresentation() {
        return representation;
    }

    /**
     * Parses function data from its AST.
     *
     * This method must not be called after the AST has been already set.
     *
     * @param rep the AST to parse.
     */
    public void parseRepresentation(DafnyTree rep) {
        assert this.representation == null
                : "A builder must not have its representation replaced";

        this.representation = rep;

        this.name = rep.getChild(0).getText();
        this.requiresClauses.addAll(rep.getChildrenWithType(DafnyParser.REQUIRES));
        this.ensuresClauses.addAll(rep.getChildrenWithType(DafnyParser.ENSURES));
        this.decreasesClause = rep.getFirstChildWithType(DafnyParser.DECREASES);
        this.params.addAll(rep.getFirstChildWithType(DafnyParser.ARGS).getChildren());
        this.returnType = rep.getFirstChildWithType(DafnyParser.RETURNS).getChild(0);
        this.expression = rep.getLastChild();
    }

    /**
     * Builds a {@link DafnyFunction} with the data from this object.
     *
     * @return a freshly created object
     */
    public DafnyFunction build() {
        return new DafnyFunction(this);
    }

    public String getFilename() {
        return filename;
    }

    public void setFilename(String filename) {
        this.filename = filename;
    }

    public List<DafnyTree> getRequiresClauses() {
        return requiresClauses;
    }

    /**
     * Adds a requires clauses to this function.
     *
     * @param requiresClause the requires clause, not <code>null</code>
     */
    public void addRequiresClauses(DafnyTree requiresClause) {
        this.requiresClauses.add(requiresClause);
    }

    public List<DafnyTree> getEnsuresClauses() {
        return ensuresClauses;
    }

    /**
     * Adds an ensuresclauses to this function.
     *
     * @param ensuresClause the ensures clause, not <code>null</code>
     */
    public void addEnsuresClause(DafnyTree ensuresClause) {
        this.ensuresClauses.add(ensuresClause);
    }

    public DafnyTree getDecreasesClause() {
        return decreasesClause;
    }

    public void setDecreasesClause(DafnyTree decreasesClause) {
        this.decreasesClause = decreasesClause;
    }

    public DafnyTree getExpression() {
        return expression;
    }

    public void setExpression(DafnyTree expression) {
        this.expression = expression;
    }

    public List<DafnyTree> getParameters() {
        return params;
    }

    /**
     * Adds a parameter to the list of function parameters.
     *
     * @param parameter the parameter, not <code>null</code>
     */
    public void addParameter(DafnyTree parameter) {
        params.add(parameter);
    }

    public DafnyTree getReturnType() {
        return returnType;
    }

    public void setReturnType(DafnyTree type) {
        this.returnType = type;
    }

    public String getName() {
        return name;
    }

    public void setName(String name) {
        this.name = name;
    }

    public boolean isInLibrary() {
        return inLibrary;
    }

    public void setInLibrary(boolean inLibrary) {
        this.inLibrary = inLibrary;
    }

}
