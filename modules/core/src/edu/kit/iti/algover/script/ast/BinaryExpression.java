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
import org.antlr.v4.runtime.ParserRuleContext;

/**
 * @author Alexander Weigl
 * @version 1 (28.04.17)
 */
public class BinaryExpression extends Expression {
    private Expression left, right;
    private Operator operator;

    public BinaryExpression() {
    }

    public BinaryExpression(Expression left, Operator operator, Expression right) {
        this.left = left;
        this.operator = operator;
        this.right = right;
    }

    @Override
    public <T> T accept(Visitor<T> visitor) {
        return visitor.visit(this);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public BinaryExpression copy() {
        BinaryExpression be = new BinaryExpression(left.copy(), operator, right.copy());
        return be;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Type getType(Signature signature) throws NotWelldefinedException {
        if (operator.arity() != 2)
            throw new NotWelldefinedException("Arity mismatch", this);

        checkType(operator.type()[0], left, signature);
        checkType(operator.type()[1], right, signature);

        return operator.returnType();
    }

    @Override
    public boolean hasMatchExpression() {
        return left.hasMatchExpression() || right.hasMatchExpression();
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public int getPrecedence() {
        return operator.precedence();
    }

    public Expression getLeft() {
        return this.left;
    }

    public void setLeft(Expression left) {
        this.left = left;
    }

    public Expression getRight() {
        return this.right;
    }

    public void setRight(Expression right) {
        this.right = right;
    }

    public Operator getOperator() {
        return this.operator;
    }

    public void setOperator(Operator operator) {
        this.operator = operator;
    }

    public boolean equals(Object o) {
        if (o == this) return true;
        if (!(o instanceof BinaryExpression)) return false;
        final BinaryExpression other = (BinaryExpression) o;
        if (!other.canEqual((Object) this)) return false;
        final Object this$left = this.getLeft();
        final Object other$left = other.getLeft();
        if (this$left == null ? other$left != null : !this$left.equals(other$left)) return false;
        final Object this$right = this.getRight();
        final Object other$right = other.getRight();
        if (this$right == null ? other$right != null : !this$right.equals(other$right)) return false;
        final Object this$operator = this.getOperator();
        final Object other$operator = other.getOperator();
        if (this$operator == null ? other$operator != null : !this$operator.equals(other$operator)) return false;
        return true;
    }

    public int hashCode() {
        final int PRIME = 59;
        int result = 1;
        final Object $left = this.getLeft();
        result = result * PRIME + ($left == null ? 43 : $left.hashCode());
        final Object $right = this.getRight();
        result = result * PRIME + ($right == null ? 43 : $right.hashCode());
        final Object $operator = this.getOperator();
        result = result * PRIME + ($operator == null ? 43 : $operator.hashCode());
        return result;
    }

    protected boolean canEqual(Object other) {
        return other instanceof BinaryExpression;
    }

    public String toString() {
        return "edu.kit.iti.algover.script.ast.BinaryExpression(left=" + this.getLeft() + ", right=" + this.getRight() + ", operator=" + this.getOperator() + ")";
    }
}
