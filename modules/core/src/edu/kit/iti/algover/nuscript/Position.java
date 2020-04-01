/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 *
 */

package edu.kit.iti.algover.nuscript;

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


import edu.kit.iti.algover.nuscript.parser.ScriptLexer;
import nonnull.NonNull;
import org.antlr.v4.runtime.CommonToken;
import org.antlr.v4.runtime.Token;

/**
 * @author Alexander Weigl
 */
public class Position implements Comparable<Position> {

    private final int lineNumber;
    private final int charInLine;

    public Position(int lineNumber, int charInLine) {
        this.lineNumber = lineNumber;
        this.charInLine = charInLine;
    }

    public static Position from(Token token) {
        if (token == null) {
            return from(new CommonToken(ScriptLexer.EOF));
        }
        return new Position(token.getLine(), token.getCharPositionInLine());
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

    public String toString() {
        return "Position(line=" + this.getLineNumber() + ", char=" + this.getCharInLine() + ")";
    }

    @Override
    public int compareTo(Position position) {
        if (getLineNumber() != position.getLineNumber()) {
            return Integer.signum(getLineNumber() - position.getLineNumber());
        } else {
            return Integer.signum(getCharInLine() - position.getCharInLine());
        }
    }
}
