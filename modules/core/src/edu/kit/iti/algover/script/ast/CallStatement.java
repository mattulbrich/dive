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

/**
 * A call to a subroutine or atomic function.
 *
 * @author Alexander Weigl
 * @version 1 (28.04.17)
 */
public class CallStatement extends Statement {
    /**
     * The name of the command.
     */
    @NonNull
    private String command;

    /**
     * The list of parameters.
     */
    private Parameters parameters = new Parameters();

    @java.beans.ConstructorProperties({"command"})
    public CallStatement(String command) {
        this.command = command;
    }

    @java.beans.ConstructorProperties({"command", "parameters"})
    public CallStatement(String command, Parameters parameters) {
        this.command = command;
        this.parameters = parameters;
    }

    public CallStatement() {
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
    public CallStatement copy() {
        return new CallStatement(command, parameters.copy());
    }

    @NonNull
    public String getCommand() {
        return this.command;
    }

    public void setCommand(@NonNull String command) {
        this.command = command;
    }

    public Parameters getParameters() {
        return this.parameters;
    }

    public void setParameters(Parameters parameters) {
        this.parameters = parameters;
    }

    public boolean equals(Object o) {
        if (o == this) return true;
        if (!(o instanceof CallStatement)) return false;
        final CallStatement other = (CallStatement) o;
        if (!other.canEqual((Object) this)) return false;
        final Object this$command = this.getCommand();
        final Object other$command = other.getCommand();
        if (this$command == null ? other$command != null : !this$command.equals(other$command)) return false;
        final Object this$parameters = this.getParameters();
        final Object other$parameters = other.getParameters();
        if (this$parameters == null ? other$parameters != null : !this$parameters.equals(other$parameters))
            return false;
        return true;
    }

    public int hashCode() {
        final int PRIME = 59;
        int result = 1;
        final Object $command = this.getCommand();
        result = result * PRIME + ($command == null ? 43 : $command.hashCode());
        final Object $parameters = this.getParameters();
        result = result * PRIME + ($parameters == null ? 43 : $parameters.hashCode());
        return result;
    }

    protected boolean canEqual(Object other) {
        return other instanceof CallStatement;
    }

    public String toString() {
        return "edu.kit.iti.algover.script.ast.CallStatement(command=" + this.getCommand() + ", parameters=" + this.getParameters() + ")";
    }
}
