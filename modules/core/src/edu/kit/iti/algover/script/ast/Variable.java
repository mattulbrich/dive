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


import edu.kit.iti.algover.script.exceptions.NotWelldefinedException;
import edu.kit.iti.algover.script.parser.Visitor;
import nonnull.NonNull;
import org.antlr.v4.runtime.Token;

/**
 * @author Alexander Weigl
 * @version 1 (28.04.17)
 */
public class Variable extends Literal implements Comparable<Variable> {
    @NonNull
    private String identifier;

    public Variable(Token variable) {
        this(variable.getText());
        setToken(variable);
    }

    @java.beans.ConstructorProperties({"identifier"})
    public Variable(String identifier) {
        this.identifier = identifier;
    }

    @Override
    public <T> T accept(Visitor<T> visitor) {
        return visitor.visit(this);
    }

    @Override
    public boolean hasMatchExpression() {
        return false;
    }

    @Override
    public Variable copy() {
        Variable v = new Variable(identifier);
        v.token = token;
        return v;
    }

    /**
     * Expression getType
     * {@inheritDoc}
     */
    @Override
    public Type getType(Signature signature) throws NotWelldefinedException {
        if (signature.containsKey(this))
            return signature.get(this);
        throw new NotWelldefinedException(toString() + "not defined in signature.", this);
    }

    @Override
    public int compareTo(Variable o) {
        return identifier.compareTo(o.getIdentifier());
    }

    @NonNull
    public String getIdentifier() {
        return this.identifier;
    }

    public void setIdentifier(@NonNull String identifier) {
        this.identifier = identifier;
    }

    public String toString() {
        return "Variable(name=" + this.getIdentifier() + ")";
    }

    public boolean equals(Object o) {
        if (o == this) return true;
        if (!(o instanceof Variable)) return false;
        final Variable other = (Variable) o;
        if (!other.canEqual((Object) this)) return false;
        final Object this$identifier = this.getIdentifier();
        final Object other$identifier = other.getIdentifier();
        if (this$identifier == null ? other$identifier != null : !this$identifier.equals(other$identifier))
            return false;
        return true;
    }

    public int hashCode() {
        final int PRIME = 59;
        int result = 1;
        final Object $identifier = this.getIdentifier();
        result = result * PRIME + ($identifier == null ? 43 : $identifier.hashCode());
        return result;
    }

    protected boolean canEqual(Object other) {
        return other instanceof Variable;
    }
}
