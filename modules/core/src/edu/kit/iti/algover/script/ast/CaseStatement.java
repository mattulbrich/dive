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
import edu.kit.iti.algover.script.parser.Visitor;

/**
 * @author Alexander Weigl
 * @version 1 (28.04.17)
 */
public class CaseStatement extends Statement<ScriptLanguageParser.CasesListContext> {
    public boolean isClosedStmt;
    protected Statements body;

    @java.beans.ConstructorProperties({"isClosedStmt", "body"})
    public CaseStatement(boolean isClosedStmt, Statements body) {
        this.isClosedStmt = isClosedStmt;
        this.body = body;
    }

    public CaseStatement() {
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
    public CaseStatement copy() {
        return new CaseStatement(isClosedStmt, body.copy());
    }

    public boolean isClosedStmt() {
        return this.isClosedStmt;
    }

    public void setClosedStmt(boolean isClosedStmt) {
        this.isClosedStmt = isClosedStmt;
    }

    public Statements getBody() {
        return this.body;
    }

    public void setBody(Statements body) {
        this.body = body;
    }

    public boolean equals(Object o) {
        if (o == this) return true;
        if (!(o instanceof CaseStatement)) return false;
        final CaseStatement other = (CaseStatement) o;
        if (!other.canEqual((Object) this)) return false;
        if (this.isClosedStmt() != other.isClosedStmt()) return false;
        final Object this$body = this.getBody();
        final Object other$body = other.getBody();
        if (this$body == null ? other$body != null : !this$body.equals(other$body)) return false;
        return true;
    }

    public int hashCode() {
        final int PRIME = 59;
        int result = 1;
        result = result * PRIME + (this.isClosedStmt() ? 79 : 97);
        final Object $body = this.getBody();
        result = result * PRIME + ($body == null ? 43 : $body.hashCode());
        return result;
    }

    protected boolean canEqual(Object other) {
        return other instanceof CaseStatement;
    }

    public String toString() {
        return "edu.kit.iti.algover.script.ast.CaseStatement(isClosedStmt=" + this.isClosedStmt() + ", body=" + this.getBody() + ")";
    }
}
