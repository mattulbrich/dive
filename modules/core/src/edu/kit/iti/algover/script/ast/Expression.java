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
import org.antlr.v4.runtime.ParserRuleContext;

/**
 * Abstract representation of an expression.
 *
 * @author Alexander Weigl
 * @version 1 (28.04.17)
 */
public abstract class Expression<T extends ParserRuleContext> extends ASTNode<T> {
    /**
     * @param type
     * @param e
     * @param signature
     * @throws NotWelldefinedException
     */
    public static final void checkType(Type type, Expression<?> e, Signature signature) throws NotWelldefinedException {
        Type got = e.getType(signature);
        if (!type.equals(got)) {
            throw new NotWelldefinedException("Typemismatch in expected " + type + ", got" + got, e);
        }
    }

    /**
     * @return returns true if a child expression contains a match expression
     */
    public abstract boolean hasMatchExpression();

    /**
     * Returns the precedence of the operator expression.
     * <p>
     * For {@link BinaryExpression} and {@link UnaryExpression}
     * this is the precedence of the operator.
     * For {@link Literal} is this zero.
     */
    public abstract int getPrecedence();

    /**
     * {@inheritDoc}
     */
    @Override
    public abstract Expression<T> copy();

    /**
     * {@inheritDoc}
     */
    public abstract Type getType(Signature signature)
            throws NotWelldefinedException;

    /**
     *
     * @return
     */
    public String  getText() {
        return this.ruleContext.getText();
    }

}
