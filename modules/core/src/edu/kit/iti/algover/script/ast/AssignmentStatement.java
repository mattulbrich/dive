package edu.kit.iti.algover.script.ast;

/*-
 * #%L
 * ProofScriptParser
 * %%
 * Copyright (C) 2017 Application-oriented Formal Verification
 * %%
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as
 * published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 * 
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 * 
 * You should have received a copy of the GNU General Public
 * License along with this program.  If not, see
 * <http://www.gnu.org/licenses/gpl-3.0.html>.
 * #L%
 */


import edu.kit.iti.algover.script.ScriptLanguageParser;
import edu.kit.iti.algover.script.parser.Visitor;
import nonnull.NonNull;

/**
 * An {@link AssignmentStatement} encapsulate the assigned variable
 * {@link AssignmentStatement#getLhs()} and an expression {@link AssignmentStatement#getRhs()}.
 *
 * @author Alexander Weigl
 * @version 1 (28.04.17)
 */

// REVIEW: Add the missing generic parameters! Please!

@SuppressWarnings({"unchecked", "rawtypes"})
public class AssignmentStatement
        extends Statement<ScriptLanguageParser.AssignmentContext> {
    @NonNull
    private Variable lhs;

    private Expression rhs;

    private Type type;

    @java.beans.ConstructorProperties({"lhs"})
    public AssignmentStatement(Variable lhs) {
        this.lhs = lhs;
    }

    @java.beans.ConstructorProperties({"lhs", "rhs", "type"})
    public AssignmentStatement(Variable lhs, Expression rhs, Type type) {
        this.lhs = lhs;
        this.rhs = rhs;
        this.type = type;
    }

    public AssignmentStatement() {
    }

    @Override
    public <T> T accept(Visitor<T> visitor) {
        return visitor.visit(this);
    }

    @Override
    public AssignmentStatement copy() {
        AssignmentStatement s = new AssignmentStatement();
        s.lhs = lhs.copy();
        s.rhs = rhs.copy();
        s.type = type;
        return s;
    }

    /**
     * Returns true, iff this assignment declares the assigned variable.
     */
    public boolean isDeclaration() {
        return type != null;
    }

    @NonNull
    public Variable getLhs() {
        return this.lhs;
    }

    public void setLhs(@NonNull Variable lhs) {
        this.lhs = lhs;
    }

    public Expression getRhs() {
        return this.rhs;
    }

    public void setRhs(Expression rhs) {
        this.rhs = rhs;
    }

    public Type getType() {
        return this.type;
    }

    public void setType(Type type) {
        this.type = type;
    }

    public boolean equals(Object o) {
        if (o == this) return true;
        if (!(o instanceof AssignmentStatement)) return false;
        final AssignmentStatement other = (AssignmentStatement) o;
        if (!other.canEqual((Object) this)) return false;
        final Object this$lhs = this.getLhs();
        final Object other$lhs = other.getLhs();
        if (this$lhs == null ? other$lhs != null : !this$lhs.equals(other$lhs)) return false;
        final Object this$rhs = this.getRhs();
        final Object other$rhs = other.getRhs();
        if (this$rhs == null ? other$rhs != null : !this$rhs.equals(other$rhs)) return false;
        final Object this$type = this.getType();
        final Object other$type = other.getType();
        if (this$type == null ? other$type != null : !this$type.equals(other$type)) return false;
        return true;
    }

    public int hashCode() {
        final int PRIME = 59;
        int result = 1;
        final Object $lhs = this.getLhs();
        result = result * PRIME + ($lhs == null ? 43 : $lhs.hashCode());
        final Object $rhs = this.getRhs();
        result = result * PRIME + ($rhs == null ? 43 : $rhs.hashCode());
        final Object $type = this.getType();
        result = result * PRIME + ($type == null ? 43 : $type.hashCode());
        return result;
    }

    protected boolean canEqual(Object other) {
        return other instanceof AssignmentStatement;
    }

    public String toString() {
        return "edu.kit.iti.algover.script.ast.AssignmentStatement(lhs=" + this.getLhs() + ", rhs=" + this.getRhs() + ", type=" + this.getType() + ")";
    }
}
