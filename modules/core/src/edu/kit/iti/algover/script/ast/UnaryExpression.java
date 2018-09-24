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
import org.antlr.v4.runtime.ParserRuleContext;

/**
 * @author Alexander Weigl
 * @author Sarah Grebing
 * @version 1 (30.04.17)
 */

// REVIEW: Add the missing generic parameters! Please!

@SuppressWarnings({"unchecked", "rawtypes"})
public class UnaryExpression extends Expression<ParserRuleContext> {
    @NonNull
    private Operator operator;
    @NonNull
    private Expression expression;

    @java.beans.ConstructorProperties({"operator", "expression"})
    public UnaryExpression(Operator operator, Expression expression) {
        this.operator = operator;
        this.expression = expression;
    }

    public UnaryExpression() {
    }

    /**
     * {@inheritDoc
     */
    @Override
    public <T> T accept(Visitor<T> visitor) {
        return visitor.visit(this);
    }

    /**
     * {@inheritDoc
     */
    @Override
    public UnaryExpression copy() {
        UnaryExpression u = new UnaryExpression(operator, expression.copy());
        return u;
    }

    /**
     * {@inheritDoc
     */
    @Override
    public Type getType(Signature signature) throws NotWelldefinedException {
        if (operator.arity() != 1)
            throw new NotWelldefinedException("Arity mismatch!", this);
        checkType(operator.type()[0], expression, signature);
        return operator.returnType();
    }

    @Override
    public boolean hasMatchExpression() {
        return expression.hasMatchExpression();
    }

    /**
     * {@inheritDoc
     */
    @Override
    public int getPrecedence() {
        return Operator.NOT.precedence();//a placeholder, because MINUS is used as binary operator,too
    }

    @NonNull
    public Operator getOperator() {
        return this.operator;
    }

    public void setOperator(@NonNull Operator operator) {
        this.operator = operator;
    }

    @NonNull
    public Expression getExpression() {
        return this.expression;
    }

    public void setExpression(@NonNull Expression expression) {
        this.expression = expression;
    }

    public boolean equals(Object o) {
        if (o == this) return true;
        if (!(o instanceof UnaryExpression)) return false;
        final UnaryExpression other = (UnaryExpression) o;
        if (!other.canEqual((Object) this)) return false;
        final Object this$operator = this.getOperator();
        final Object other$operator = other.getOperator();
        if (this$operator == null ? other$operator != null : !this$operator.equals(other$operator)) return false;
        final Object this$expression = this.getExpression();
        final Object other$expression = other.getExpression();
        if (this$expression == null ? other$expression != null : !this$expression.equals(other$expression))
            return false;
        return true;
    }

    public int hashCode() {
        final int PRIME = 59;
        int result = 1;
        final Object $operator = this.getOperator();
        result = result * PRIME + ($operator == null ? 43 : $operator.hashCode());
        final Object $expression = this.getExpression();
        result = result * PRIME + ($expression == null ? 43 : $expression.hashCode());
        return result;
    }

    protected boolean canEqual(Object other) {
        return other instanceof UnaryExpression;
    }

    public String toString() {
        return "edu.kit.iti.algover.script.ast.UnaryExpression(operator=" + this.getOperator() + ", expression=" + this.getExpression() + ")";
    }
}
