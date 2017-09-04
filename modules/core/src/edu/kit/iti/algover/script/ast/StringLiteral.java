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

/**
 * @author Alexander Weigl
 * @version 1 (28.04.17)
 */
public class StringLiteral extends Literal {
    private final String text;

    public StringLiteral(String text) {
        if (text.charAt(0) == '\'')
            text = text.substring(1);
        if (text.charAt(text.length() - 1) == '\'')
            text = text.substring(0, text.length() - 1);
        this.text = text;
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
    public StringLiteral copy() {
        return new StringLiteral(text);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Type getType(Signature signature) throws NotWelldefinedException {
        return Type.STRING;
    }

    public String getText() {
        return this.text;
    }

    public boolean equals(Object o) {
        if (o == this) return true;
        if (!(o instanceof StringLiteral)) return false;
        final StringLiteral other = (StringLiteral) o;
        if (!other.canEqual((Object) this)) return false;
        final Object this$text = this.getText();
        final Object other$text = other.getText();
        if (this$text == null ? other$text != null : !this$text.equals(other$text)) return false;
        return true;
    }

    public int hashCode() {
        final int PRIME = 59;
        int result = 1;
        final Object $text = this.getText();
        result = result * PRIME + ($text == null ? 43 : $text.hashCode());
        return result;
    }

    protected boolean canEqual(Object other) {
        return other instanceof StringLiteral;
    }

    public String toString() {
        return "edu.kit.iti.algover.script.ast.StringLiteral(text=" + this.getText() + ")";
    }
}
