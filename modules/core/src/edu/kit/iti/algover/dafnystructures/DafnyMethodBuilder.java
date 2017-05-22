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

public class DafnyMethodBuilder {

    private DafnyTree representation;
    private String filename;
    private String name;
    private List<DafnyTree> params = new ArrayList<>();
    private List<DafnyTree> returns = new ArrayList<>();
    private List<DafnyTree> requiresClauses = new ArrayList<>();
    private List<DafnyTree> ensuresClauses = new ArrayList<>();
    private DafnyTree decreasesClause;
    private DafnyTree modifiesClause;
    private DafnyTree body;
    private boolean inLibrary;

    public DafnyMethodBuilder(String filename, DafnyTree child) {
        setFilename(filename);
        parseRepresentation(child);
    }

    public DafnyMethodBuilder(String filename) {
        setFilename(filename);
    }

    public DafnyMethodBuilder() {
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
        this.modifiesClause = rep.getFirstChildWithType(DafnyParser.MODIFIES);
        this.params.addAll(rep.getFirstChildWithType(DafnyParser.ARGS).getChildren());
        DafnyTree returns = rep.getFirstChildWithType(DafnyParser.RETURNS);
        if(returns != null) {
            this.returns.addAll(returns.getChildren());
        }
        this.body = rep.getFirstChildWithType(DafnyParser.BLOCK);
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

    public DafnyTree getModifiesClause() {
        return modifiesClause;
    }

    public void setModifiesClause(DafnyTree modifiesClause) {
        this.modifiesClause = modifiesClause;
    }

    public DafnyTree getBody() {
        return body;
    }

    public void setBody(DafnyTree body) {
        this.body = body;
    }

    public DafnyMethod build() {
        return new DafnyMethod(this);
    }

    public List<DafnyTree> getParameters() {
        return params;
    }

    public void addParameter(DafnyTree parameter) {
        params.add(parameter);
    }

    public List<DafnyTree> getReturns() {
        return returns;
    }

    public void addReturn(DafnyTree ret) {
        returns.add(ret);
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
