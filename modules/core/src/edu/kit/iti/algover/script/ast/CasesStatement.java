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


import edu.kit.iti.algover.script.ScriptLanguageParser;
import edu.kit.iti.algover.script.parser.Visitor;
import nonnull.NonNull;

import java.util.ArrayList;
import java.util.List;

/**
 * @author Alexander Weigl
 * @version 1 (28.04.17)
 */
public class CasesStatement extends Statement {
    @NonNull
    private final List<CaseStatement> cases = new ArrayList<>();
    @NonNull
    private Statements defaultCase = new Statements();

    public CasesStatement() {
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
    public CasesStatement copy() {
        CasesStatement c = new CasesStatement();
        cases.forEach(caseStatement -> c.cases.add(caseStatement.copy()));
        if (defaultCase != null)
            c.defaultCase = defaultCase.copy();
        return c;
    }

    @NonNull
    public List<CaseStatement> getCases() {
        return this.cases;
    }

    @NonNull
    public Statements getDefaultCase() {
        return this.defaultCase;
    }

    public void setDefaultCase(@NonNull Statements defaultCase) {
        this.defaultCase = defaultCase;
    }

    public boolean equals(Object o) {
        if (o == this) return true;
        if (!(o instanceof CasesStatement)) return false;
        final CasesStatement other = (CasesStatement) o;
        if (!other.canEqual((Object) this)) return false;
        final Object this$cases = this.getCases();
        final Object other$cases = other.getCases();
        if (this$cases == null ? other$cases != null : !this$cases.equals(other$cases)) return false;
        final Object this$defaultCase = this.getDefaultCase();
        final Object other$defaultCase = other.getDefaultCase();
        if (this$defaultCase == null ? other$defaultCase != null : !this$defaultCase.equals(other$defaultCase))
            return false;
        return true;
    }

    public int hashCode() {
        final int PRIME = 59;
        int result = 1;
        final Object $cases = this.getCases();
        result = result * PRIME + ($cases == null ? 43 : $cases.hashCode());
        final Object $defaultCase = this.getDefaultCase();
        result = result * PRIME + ($defaultCase == null ? 43 : $defaultCase.hashCode());
        return result;
    }

    protected boolean canEqual(Object other) {
        return other instanceof CasesStatement;
    }

    public String toString() {
        return "edu.kit.iti.algover.script.ast.CasesStatement(cases=" + this.getCases() + ", defaultCase=" + this.getDefaultCase() + ")";
    }
}
