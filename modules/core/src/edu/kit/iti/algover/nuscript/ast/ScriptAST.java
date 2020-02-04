/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 *
 */

package edu.kit.iti.algover.nuscript.ast;

import edu.kit.iti.algover.nuscript.ScriptException;
import edu.kit.iti.algover.util.FunctionWithException;
import org.antlr.v4.runtime.Token;

import java.util.LinkedList;
import java.util.List;
import java.util.function.BiFunction;
import java.util.function.Function;

public abstract class ScriptAST {

    public static class Script extends ScriptAST {
        private List<Statement> statements = new LinkedList<>();
        public List<Statement> getStatements() {
            return statements;
        }
        public void addStatement(Statement stmt) {
            statements.add(stmt);
        }
    }

    public static class Statement extends ScriptAST {
        // poor man's version of a visitor....
        // should there be more cases in the future consider using a proper visitor.
        public <R> R doCommandOrCases(
                FunctionWithException<Command, R, ScriptException> commandFct,
                FunctionWithException<Cases, R, ScriptException> casesFct) throws ScriptException {
            if (this instanceof Command) {
                Command command = (Command) this;
                return commandFct.apply(command);
            } else {
                Cases cases = (Cases)this;
                return casesFct.apply(cases);
            }
        }

    }

    public static class Command extends Statement {
        private Token command;
        private List<Parameter> parameters;

        public void setCommand(Token command) {
            this.command = command;
        }

        public Token getCommand() {
            return command;
        }

        public void addParameter(Parameter p) {
            parameters.add(p);
        }
    }

    public static class Parameter extends ScriptAST {
        private Token name;
        private Token value;

        public void setName(Token name) {
            this.name = name;
        }

        public Token getName() {
            return name;
        }

        public void setValue(Token value) {
            this.value = value;
        }

        public Token getValue() {
            return value;
        }
    }

    public static class Cases extends Statement {
        private List<Case> cases = new LinkedList<>();

        public void addCase(Case cas) {
            cases.add(cas);
        }
    }

    public static class Case extends ScriptAST {
        private Token label;
        private List<Statement> statements = new LinkedList<>();

        public void setLabel(Token label) {
            this.label = label;
        }

        public Token getLabel() {
            return label;
        }

        public void addStatement(Statement stmt) {
            statements.add(stmt);
        }
    }


}
