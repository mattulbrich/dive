/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
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
import org.antlr.v4.runtime.Token;

/**
 * Represents a boolean literal (ie. {@link #FALSE} or {@link #TRUE}).
 * <p>
 * Instantiating can be useful for setting a custom {@link #setToken(Token)} and position.
 *
 * @author Alexander Weigl
 * @version 1 (28.04.17)
 */
public class BooleanLiteral extends Literal {
    public static final BooleanLiteral FALSE = new BooleanLiteral(false);
    public static final BooleanLiteral TRUE = new BooleanLiteral(true);

    private final boolean value;

    public BooleanLiteral(boolean value, Token token) {
        this.value = value;
        this.token = token;
    }

    BooleanLiteral(boolean b) {
        this(b, null);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public <T> T accept(Visitor<T> visitor) {
        return visitor.visit(this);
    }

    @Override
    public boolean hasMatchExpression() {
        return false;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public BooleanLiteral copy() {
        return new BooleanLiteral(value, token);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Type getType(Signature signature) throws NotWelldefinedException {
        return Type.BOOL;
    }

    public String toString() {
        return "edu.kit.iti.algover.script.ast.BooleanLiteral(value=" + this.isValue() + ")";
    }

    public boolean isValue() {
        return this.value;
    }

    public boolean equals(Object o) {
        if (o == this) return true;
        if (!(o instanceof BooleanLiteral)) return false;
        final BooleanLiteral other = (BooleanLiteral) o;
        if (!other.canEqual((Object) this)) return false;
        if (this.isValue() != other.isValue()) return false;
        return true;
    }

    public int hashCode() {
        final int PRIME = 59;
        int result = 1;
        result = result * PRIME + (this.isValue() ? 79 : 97);
        return result;
    }

    protected boolean canEqual(Object other) {
        return other instanceof BooleanLiteral;
    }
}
