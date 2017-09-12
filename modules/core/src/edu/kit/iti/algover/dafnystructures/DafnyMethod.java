/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.dafnystructures;

import edu.kit.iti.algover.parser.DafnyTree;

import java.util.Collections;
import java.util.List;

/**
 * A method in Dafny. It may be either in a class or standalone in a file.
 */
public class DafnyMethod extends DafnyDecl {
    /**
     * The parameter declarations of this method.
     * Not <code>null</code>, but may be empty.
     */
    private final List<DafnyTree> params;

    /**
     * The return variable declarations.
     */
    private final List<DafnyTree> returns;

    /**
     * The collection of requires clauses.
     * May be empty but not <code>null</code>.
     */
    private final List<DafnyTree> requiresClauses;

    /**
     * The collection of ensures clauses.
     * May be empty but not <code>null</code>.
     */
    private final List<DafnyTree> ensuresClauses;

    /**
     * The decreases clauses for termination of this method
     * May be <code>null</code>.
     */
    private final DafnyTree decreasesClause;

    /**
     * The modifies clauses for framing of of this method
     * May be <code>null</code>.
     */
    private final DafnyTree modifiesClause;

    /**
     * The code body. Must eventually be set.
     */
    private final DafnyTree body;

    /**
     * Instantiates a new dafny method from the data in a builder.
     *
     * @param b
     *            the builder, not <code>null</code>
     */
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


    public List<DafnyTree> getParams() {
        return Collections.unmodifiableList(params);
    }

    public List<DafnyTree> getReturns() {
        return Collections.unmodifiableList(returns);
    }

    public DafnyTree getBody() {
        return body;
    }

    public List<DafnyTree> getRequiresClauses() {
        return Collections.unmodifiableList(requiresClauses);
    }

    public List<DafnyTree> getEnsuresClauses() {
        return Collections.unmodifiableList(ensuresClauses);
    }

    public DafnyTree getDecreasesClause() {
        return decreasesClause;
    }

    public DafnyTree getModifiesClause() {
        return modifiesClause;
    }

    // REVIEW: toString(/) shouldbe oneliner
    @Override
    public String toString() {
        String s = "method " + this.getName(); // + "\n";
//
//        if (this.params != null) {
//            String params = this.params.size() + " Parameters: ";
//
//            for (DafnyTree para : this.params) {
//                params += para.toStringTree() + "\n";
//            }
//            s += params + "\n";
//        }
        return s;

    }

    @Override
    public <R, A> R accept(DafnyDeclVisitor<R, A> visitor, A arg) {
        return visitor.visit(this, arg);
    }

}
