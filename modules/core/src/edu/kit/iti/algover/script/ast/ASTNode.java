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


import edu.kit.iti.algover.script.parser.Visitable;
import edu.kit.iti.algover.script.parser.Visitor;
import org.antlr.v4.runtime.ParserRuleContext;

/**
 * @author Alexander Weigl
 * @version 1 (27.04.17)
 */
public abstract class ASTNode<T extends ParserRuleContext>
        implements Visitable, Copyable<ASTNode<T>> {
    /**
     * The corresponding parse rule context
     */
    protected T ruleContext;

    /**
     *
     */
    protected Position startPosition = new Position();

    /**
     *
     */
    protected Position endPosition = new Position();

    /**
     * Returns the sourceName which defined this ast node or null
     *
     * @return
     */
    public String getOrigin() {
        if (ruleContext != null) {
            String src = ruleContext.getStart().getInputStream().getSourceName();
            return src;
        }
        return null;
    }

    public T getRuleContext() {
        return ruleContext;
    }

    public void setRuleContext(T c) {
        startPosition = Position.from(c.getStart());
        endPosition = Position.from(c.getStop());
        ruleContext = c;
    }

    public Position getStartPosition() {
        return startPosition;
    }

    public Position getEndPosition() {
        return endPosition;
    }

    /**
     * <p>getNodeName.</p>
     *
     * @return a {@link String} object.
     */
    public String getNodeName() {
        return getClass().getSimpleName();
    }

    /**
     * {@inheritDoc}
     */
    public abstract <T> T accept(Visitor<T> visitor);

    /**
     * Deep copy of the AST hierarchy.
     *
     * @return a fresh substree of the AST that is equal to this.
     */
    @Override
    public abstract ASTNode<T> copy();

}
