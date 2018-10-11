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
import org.antlr.v4.runtime.ParserRuleContext;

/**
 * @author Alexander Weigl
 * @version 1 (29.04.17)
 */

// REVIEW: Add the missing generic parameters! Please!

@SuppressWarnings({"unchecked", "rawtypes"})
public abstract class GoalSelector<T extends ParserRuleContext>
        extends Statement<T> {
    @NonNull
    private Statements body = new Statements();

    @java.beans.ConstructorProperties({"body"})
    public GoalSelector(Statements body) {
        this.body = body;
    }

    public GoalSelector() {
    }

    @NonNull
    public Statements getBody() {
        return this.body;
    }

    public void setBody(@NonNull Statements body) {
        this.body = body;
    }

    public boolean equals(Object o) {
        if (o == this) return true;
        if (!(o instanceof GoalSelector)) return false;
        final GoalSelector other = (GoalSelector) o;
        if (!other.canEqual((Object) this)) return false;
        final Object this$body = this.getBody();
        final Object other$body = other.getBody();
        if (this$body == null ? other$body != null : !this$body.equals(other$body)) return false;
        return true;
    }

    public int hashCode() {
        final int PRIME = 59;
        int result = 1;
        final Object $body = this.getBody();
        result = result * PRIME + ($body == null ? 43 : $body.hashCode());
        return result;
    }

    protected boolean canEqual(Object other) {
        return other instanceof GoalSelector;
    }

    public String toString() {
        return "edu.kit.iti.algover.script.ast.GoalSelector(body=" + this.getBody() + ")";
    }
}
