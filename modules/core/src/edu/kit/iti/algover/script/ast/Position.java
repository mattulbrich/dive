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


import nonnull.NonNull;
import org.antlr.v4.runtime.Token;

/**
 * @author Alexander Weigl
 */
public class Position implements Copyable<Position> {
    @NonNull
    final int lineNumber;
    @NonNull
    final int charInLine;

    public Position() {
        this(-1, -1);
    }

    @java.beans.ConstructorProperties({"lineNumber", "charInLine"})
    public Position(int lineNumber, int charInLine) {
        this.lineNumber = lineNumber;
        this.charInLine = charInLine;
    }

    public static Position from(Token token) {
        return new Position(token.getLine(), token.getCharPositionInLine());
    }

    @Override
    public Position copy() {
        return new Position(lineNumber, charInLine);
    }

    @NonNull
    public int getLineNumber() {
        return this.lineNumber;
    }

    @NonNull
    public int getCharInLine() {
        return this.charInLine;
    }

    public boolean equals(Object o) {
        if (o == this) return true;
        if (!(o instanceof Position)) return false;
        final Position other = (Position) o;
        if (!other.canEqual((Object) this)) return false;
        if (this.getLineNumber() != other.getLineNumber()) return false;
        if (this.getCharInLine() != other.getCharInLine()) return false;
        return true;
    }

    public int hashCode() {
        final int PRIME = 59;
        int result = 1;
        result = result * PRIME + this.getLineNumber();
        result = result * PRIME + this.getCharInLine();
        return result;
    }

    protected boolean canEqual(Object other) {
        return other instanceof Position;
    }

    public String toString() {
        return "edu.kit.iti.algover.script.ast.Position(lineNumber=" + this.getLineNumber() + ", charInLine=" + this.getCharInLine() + ")";
    }
}
