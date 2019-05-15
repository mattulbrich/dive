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

/**
 * @author Alexander Weigl
 * @version 1 (27.04.17)
 */
public class ProofScript extends ASTNode {
    @NonNull
    private String name = "_";
    private Signature signature = new Signature();
    private Statements body = new Statements();
    private boolean isNamedScript = false;

    public ProofScript() {
    }

    @Override
    public <T> T accept(Visitor<T> visitor) {
        return visitor.visit(this);
    }

    @Override
    public ProofScript copy() {
        ProofScript ps = new ProofScript();
        ps.setName(getName());
        ps.setBody(body.copy());
        ps.setSignature(signature.copy());
        return ps;
    }


    public Signature getSignature() {
        return this.signature;
    }

    public void setSignature(Signature signature) {
        this.signature = signature;
    }

    public Statements getBody() {
        return this.body;
    }

    public void setBody(Statements body) {
        this.body = body;
    }

    public boolean equals(Object o) {
        if (o == this) return true;
        if (!(o instanceof ProofScript)) return false;
        final ProofScript other = (ProofScript) o;
        if (!other.canEqual((Object) this)) return false;
        final Object this$name = this.getName();
        final Object other$name = other.getName();
        if (this$name == null ? other$name != null : !this$name.equals(other$name)) return false;
        final Object this$signature = this.getSignature();
        final Object other$signature = other.getSignature();
        if (this$signature == null ? other$signature != null : !this$signature.equals(other$signature)) return false;
        final Object this$body = this.getBody();
        final Object other$body = other.getBody();
        if (this$body == null ? other$body != null : !this$body.equals(other$body)) return false;
        return true;
    }

    public int hashCode() {
        final int PRIME = 59;
        int result = 1;
        final Object $name = this.getName();
        result = result * PRIME + ($name == null ? 43 : $name.hashCode());
        final Object $signature = this.getSignature();
        result = result * PRIME + ($signature == null ? 43 : $signature.hashCode());
        final Object $body = this.getBody();
        result = result * PRIME + ($body == null ? 43 : $body.hashCode());
        return result;
    }

    protected boolean canEqual(Object other) {
        return other instanceof ProofScript;
    }

    public String toString() {
        return "edu.kit.iti.algover.script.ast.ProofScript(name=" + this.getName() + ", signature=" + this.getSignature() + ", body=" + this.getBody() + ")";
    }

    @NonNull
    public String getName() {
        return this.name;
    }

    public void setName(String name) {
        if (name == null) {
            this.name = " ";
        } else {
            this.name = name;

        }

    }

    public boolean isNamedScript() {
        return isNamedScript;
    }

    public void setNamedScript(boolean namedScript) {
        isNamedScript = namedScript;
    }
}
