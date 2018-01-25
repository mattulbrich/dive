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
import edu.kit.iti.algover.script.exceptions.NotWelldefinedException;
import edu.kit.iti.algover.script.parser.Visitor;

/**
 * A match expression contains an argument and a uses clause.
 *
 * @author Alexander Weigl
 * @version 1 (28.04.17)
 */
public class MatchExpression extends Expression<ScriptLanguageParser.MatchPatternContext> {
    private Signature signature = new Signature();
    private Expression pattern;
    private boolean isDerivable;
    private Expression derivableTerm;

    public MatchExpression() {
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
    public MatchExpression copy() {
        MatchExpression me = new MatchExpression();
        if (signature != null)
            me.signature = signature.copy();
        me.pattern = pattern.copy();
        return me;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Type getType(Signature signature) throws NotWelldefinedException {
        Type patternType = pattern.getType(signature);
        switch (patternType) {
            case TERM:
            case STRING:
                break;
            default:
                throw new NotWelldefinedException("Missing parameter", this);
        }

        return Type.BOOL;
    }

    @Override
    public boolean hasMatchExpression() {
        return true;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public int getPrecedence() {
        return Operator.MATCH.precedence();
    }

    public Signature getSignature() {
        return this.signature;
    }

    public void setSignature(Signature signature) {
        this.signature = signature;
    }

    public Expression getPattern() {
        return this.pattern;
    }

    public void setPattern(Expression pattern) {
        this.pattern = pattern;
    }

    public boolean equals(Object o) {
        if (o == this) return true;
        if (!(o instanceof MatchExpression)) return false;
        final MatchExpression other = (MatchExpression) o;
        if (!other.canEqual((Object) this)) return false;
        final Object this$signature = this.getSignature();
        final Object other$signature = other.getSignature();
        if (this$signature == null ? other$signature != null : !this$signature.equals(other$signature)) return false;
        final Object this$pattern = this.getPattern();
        final Object other$pattern = other.getPattern();
        if (this$pattern == null ? other$pattern != null : !this$pattern.equals(other$pattern)) return false;
        if (this.isDerivable() != other.isDerivable()) return false;
        final Object this$derivableTerm = this.getDerivableTerm();
        final Object other$derivableTerm = other.getDerivableTerm();
        if (this$derivableTerm == null ? other$derivableTerm != null : !this$derivableTerm.equals(other$derivableTerm))
            return false;
        return true;
    }

    public int hashCode() {
        final int PRIME = 59;
        int result = 1;
        final Object $signature = this.getSignature();
        result = result * PRIME + ($signature == null ? 43 : $signature.hashCode());
        final Object $pattern = this.getPattern();
        result = result * PRIME + ($pattern == null ? 43 : $pattern.hashCode());
        result = result * PRIME + (this.isDerivable() ? 79 : 97);
        final Object $derivableTerm = this.getDerivableTerm();
        result = result * PRIME + ($derivableTerm == null ? 43 : $derivableTerm.hashCode());
        return result;
    }

    protected boolean canEqual(Object other) {
        return other instanceof MatchExpression;
    }

    public String toString() {
        return "MatchExpression(signature=" + this.getSignature() + ", pattern=" + this.getPattern() + ", isDerivable=" + this.isDerivable() + ", derivableTerm=" + this.getDerivableTerm() + ")";
    }

    public boolean isDerivable() {
        return this.isDerivable;
    }

    public void setDerivable(boolean isDerivable) {
        this.isDerivable = isDerivable;
    }

    public Expression getDerivableTerm() {
        return this.derivableTerm;
    }

    public void setDerivableTerm(Expression derivableTerm) {
        this.derivableTerm = derivableTerm;
    }
}
