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

public class DafnyFunctionBuilder {

    private DafnyTree representation;
    private String filename;
    private String name;
    private List<DafnyTree> params = new ArrayList<>();
    private DafnyTree returnType;
    private List<DafnyTree> requiresClauses = new ArrayList<>();
    private List<DafnyTree> ensuresClauses = new ArrayList<>();
    private DafnyTree decreasesClause;
    private DafnyTree expression;
    private boolean inLibrary;

    public DafnyFunctionBuilder(String filename, DafnyTree child) {
        setFilename(filename);
        parseRepresentation(child);
    }

    public DafnyFunctionBuilder(String filename) {
        setFilename(filename);
    }

    public DafnyFunctionBuilder() {
        // TODO Auto-generated constructor stub
    }

    public DafnyTree getRepresentation() {
        return representation;
    }

    public void parseRepresentation(DafnyTree rep) {
        assert this.representation == null : "TODO";

        this.representation = rep;

        this.name = rep.getChild(0).getText();
        this.requiresClauses.addAll(rep.getChildrenWithType(DafnyParser.REQUIRES));
        this.ensuresClauses.addAll(rep.getChildrenWithType(DafnyParser.ENSURES));
        this.decreasesClause = rep.getFirstChildWithType(DafnyParser.DECREASES);
        this.params.addAll(rep.getFirstChildWithType(DafnyParser.ARGS).getChildren());
        this.returnType = null; // XXX
        this.expression = rep.getLastChild();
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

    public void setRequiresClauses(List<DafnyTree> requiresClauses) {
        this.requiresClauses = requiresClauses;
    }

    public List<DafnyTree> getEnsuresClauses() {
        return ensuresClauses;
    }

    public void setEnsuresClauses(List<DafnyTree> ensuresClauses) {
        this.ensuresClauses = ensuresClauses;
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

    public DafnyFunction build() {
        return new DafnyFunction(this);
    }

    public List<DafnyTree> getParameters() {
        return params;
    }

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
