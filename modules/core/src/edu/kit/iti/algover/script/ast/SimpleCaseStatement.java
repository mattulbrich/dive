package edu.kit.iti.algover.script.ast;

import edu.kit.iti.algover.script.parser.Visitor;

/**
 * Created by sarah on 7/17/17.
 */
public class SimpleCaseStatement extends CaseStatement {
    private Expression guard;
    private boolean isClosedStmt = false;

    public SimpleCaseStatement(Expression guard, Statements body) {
        this.guard = guard;
        this.body = body;
    }

    @java.beans.ConstructorProperties({"guard", "isClosedStmt"})
    public SimpleCaseStatement(Expression guard, boolean isClosedStmt) {
        this.guard = guard;
        this.isClosedStmt = isClosedStmt;
    }

    public SimpleCaseStatement() {
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
    public SimpleCaseStatement copy() {
        return new SimpleCaseStatement(guard.copy(), body.copy());
    }


    public Expression getGuard() {
        return this.guard;
    }

    public void setGuard(Expression guard) {
        this.guard = guard;
    }

    public boolean isClosedStmt() {
        return this.isClosedStmt;
    }

    public void setClosedStmt(boolean isClosedStmt) {
        this.isClosedStmt = isClosedStmt;
    }

    public boolean equals(Object o) {
        if (o == this) return true;
        if (!(o instanceof SimpleCaseStatement)) return false;
        final SimpleCaseStatement other = (SimpleCaseStatement) o;
        if (!other.canEqual((Object) this)) return false;
        final Object this$guard = this.getGuard();
        final Object other$guard = other.getGuard();
        if (this$guard == null ? other$guard != null : !this$guard.equals(other$guard)) return false;
        if (this.isClosedStmt() != other.isClosedStmt()) return false;
        return true;
    }

    public int hashCode() {
        final int PRIME = 59;
        int result = 1;
        final Object $guard = this.getGuard();
        result = result * PRIME + ($guard == null ? 43 : $guard.hashCode());
        result = result * PRIME + (this.isClosedStmt() ? 79 : 97);
        return result;
    }

    protected boolean canEqual(Object other) {
        return other instanceof SimpleCaseStatement;
    }

    public String toString() {
        return "edu.kit.iti.algover.script.ast.SimpleCaseStatement(guard=" + this.getGuard() + ", isClosedStmt=" + this.isClosedStmt() + ")";
    }
}
