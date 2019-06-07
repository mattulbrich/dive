/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.script.ast;

import edu.kit.iti.algover.script.parser.Visitor;

/**
 * Object representing  a "match isClosable{ Commands}" block
 */
public class IsClosableCase extends CaseStatement {
    private boolean isClosedStmt = true;

    public IsClosableCase(Statements body) {
        this.body = body;
    }

    public IsClosableCase() {
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public <T> T accept(Visitor<T> visitor) {
        return visitor.visit(this);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public IsClosableCase copy() {
        return new IsClosableCase(body.copy());
    }

    public boolean isClosedStmt() {
        return this.isClosedStmt;
    }

    public void setClosedStmt(boolean isClosedStmt) {
        this.isClosedStmt = isClosedStmt;
    }

    public boolean equals(Object o) {
        if (o == this) return true;
        if (!(o instanceof IsClosableCase)) return false;
        final IsClosableCase other = (IsClosableCase) o;
        if (!other.canEqual((Object) this)) return false;
        if (this.isClosedStmt() != other.isClosedStmt()) return false;
        return true;
    }

    public int hashCode() {
        final int PRIME = 59;
        int result = 1;
        result = result * PRIME + (this.isClosedStmt() ? 79 : 97);
        return result;
    }

    protected boolean canEqual(Object other) {
        return other instanceof IsClosableCase;
    }

    public String toString() {
        return "edu.kit.iti.algover.script.ast.IsClosableCase(isClosedStmt=" + this.isClosedStmt() + ")";
    }
}
