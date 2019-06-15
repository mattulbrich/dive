/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.dafnystructures;

import java.util.Collections;
import java.util.List;
import java.util.Objects;

import edu.kit.iti.algover.parser.DafnyTree;

/**
 * Class representing a single Dafny function. A function has zero or more
 * arguments, a return type, zero or more contracts and a body.
 * The decreases clause is an optional clause.
 */
public class DafnyFunction extends DafnyDecl {

    /**
     * The parameter declarations of this function.
     * Not <code>null</code>, but may be empty.
     */
    private final List<DafnyTree> params;

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
     * The decreases clauses for termination of this function
     * May be <code>null</code>.
     */
    private final DafnyTree decreasesClause;

    /**
     * The expression in the body of the function
     * not <code>null</code>.
     */
    private final DafnyTree expression;

    /**
     * The result type of the function. Non-<code>null</code>.
     */
    private final DafnyTree returnType;

    /**
     * Instantiates a new function from a builder object.
     *
     * @param b
     *            the non-<code>null</code> builder to take the data from.
     * @see DafnyFunctionBuilder
     */
    public DafnyFunction(DafnyFunctionBuilder b) {
        super(b.getFilename(), b.getRepresentation(), b.getName(), b.isInLibrary());
        this.params = Objects.requireNonNull(b.getParameters());
        this.ensuresClauses = Objects.requireNonNull(b.getEnsuresClauses());
        this.requiresClauses = Objects.requireNonNull(b.getRequiresClauses());
        this.expression = Objects.requireNonNull(b.getExpression());
        this.decreasesClause = b.getDecreasesClause();
        this.returnType = b.getReturnType();
    }

    public List<DafnyTree> getParameters() {
        return Collections.unmodifiableList(params);
    }

    public DafnyTree getReturnType() {
        return returnType;
    }

    public DafnyTree getExpression() {
        return expression;
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

    @Override
    public <R, A> R accept(DafnyDeclVisitor<R, A> visitor, A arg) {
        return visitor.visit(this, arg);
    }

    @Override
    public String toString() {
        // REVIEW. Reconsider after changes. Use StringBuilder.
        String s = "function " + this.getName() + "\n";

        if (this.getParameters() != null) {
            String params = this.getParameters().size() + " Parameters: ";

            for (DafnyTree para : this.getParameters()) {
                params += para.toStringTree() + "\n";
            }
            s += params + "\n";
        }
        //        s += "returns "+this.returnType.toStringTree()+"\n";
        //        s += "with body \n"+this.body.toStringTree();

        return s;
    }
}
