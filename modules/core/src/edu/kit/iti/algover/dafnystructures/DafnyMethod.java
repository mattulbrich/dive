/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.dafnystructures;

import edu.kit.iti.algover.parser.DafnyTree;

import java.io.File;
import java.util.List;

public class DafnyMethod extends DafnyDecl {

    private final List<DafnyTree> params;
    private final List<DafnyTree> returns;
    private final List<DafnyTree> requiresClauses;
    private final List<DafnyTree> ensuresClauses;
    private final DafnyTree decreasesClause;
    private final DafnyTree modifiesClause;
    private final DafnyTree body;

    public List<DafnyTree> getParams() {
        return params;
    }

    public List<DafnyTree> getReturns() {
        return returns;
    }

    public DafnyTree getBody() {
        return body;
    }

    public DafnyMethod(DafnyMethodBuilder b) {
        super(b.getFilename(), b.getRepresentation(), b.getName(), b.isInLibrary());
        this.requiresClauses = b.getRequiresClauses();
        this.ensuresClauses = b.getEnsuresClauses();
        this.decreasesClause = b.getDecreasesClause();
        this.modifiesClause = b.getModifiesClause();
        this.params = b.getParameters();
        this.returns = b.getReturns();
        this.body = b.getBody();
    }

    public static DafnyMethod fromTree(String filename, DafnyTree tree) {
        return new DafnyMethod(new DafnyMethodBuilder(filename, tree));
    }

    public String toString() {
        String s = "method " + this.getName() + "\n";

        if (this.params != null) {
            String params = this.params.size() + " Parameters: ";

            for (DafnyTree para : this.params) {
                params += para.toStringTree() + "\n";
            }
            s += params + "\n";
        }
        return s;

    }
    @Override
    public <R, A> R accept(DafnyDeclVisitor<R,A> visitor, A arg) {
        return visitor.visit(this, arg);
    }

}
