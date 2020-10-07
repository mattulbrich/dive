/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 *
 */

package edu.kit.iti.algover.nuscript.ast;

import edu.kit.iti.algover.nuscript.Position;
import edu.kit.iti.algover.nuscript.ScriptException;
import edu.kit.iti.algover.nuscript.parser.ScriptParser.SingleCaseContext;
import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.util.Conditional;
import edu.kit.iti.algover.util.FunctionWithException;
import edu.kit.iti.algover.util.Util;
import org.antlr.v4.runtime.ParserRuleContext;
import org.antlr.v4.runtime.Token;

import java.io.IOException;
import java.io.Writer;
import java.util.ArrayList;
import java.util.Collection;
import java.util.LinkedList;
import java.util.List;
import java.util.Objects;
import java.util.concurrent.atomic.AtomicBoolean;
import java.util.function.BiFunction;
import java.util.function.Function;

public abstract class ScriptAST {

    private Token end;
    private Token begin;

    public void setRangeFrom(ParserRuleContext ctx) {
        this.begin = ctx.start;
        this.end = ctx.stop;
    }

    public Token getBeginToken() {
        return begin;
    }

    public Position getPosition() {
        return new Position(begin.getLine(), begin.getCharPositionInLine());
    }

    public Token getEndToken() {
        return end;
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        try {
            print(sb, 0);
            return sb.toString();
        } catch (IOException e) {
            e.printStackTrace();
            return Objects.toString(this);
        }
    }

    public abstract void print(Appendable writer, int indentation) throws IOException;

    public static class Script extends ScriptAST {
        private List<Statement> statements = new LinkedList<>();
        public List<Statement> getStatements() {
            return statements;
        }
        public void addStatement(Statement stmt) {
            statements.add(stmt);
        }

        public <R> void visit(FunctionWithException<Command, R, ScriptException> commandFct,
                FunctionWithException<Cases, R, ScriptException> casesFct) throws ScriptException {
            for (Statement statement : statements) {
                statement.visit(commandFct, casesFct);
            }
        }

        public void print(Appendable writer, int indentation) throws IOException {
            Conditional conditional = Conditional.notAtFirst();
            for (Statement statement : statements) {
                conditional.run(() -> writer.append("\n"));
                statement.print(writer, indentation);
            }
        }
    }

    public abstract static class Statement extends ScriptAST {
        // poor man's version of a visitor....
        // should there be more cases in the future consider using a proper visitor.
        public <R, Ex extends Exception> R visit(
                FunctionWithException<Command, R, Ex> commandFct,
                FunctionWithException<Cases, R, Ex> casesFct) throws Ex {
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
        private List<Parameter> parameters = new ArrayList<>();
        private ProofNode proofNode;

        public void setCommand(Token command) {
            this.command = command;
        }

        public Token getCommand() {
            return command;
        }

        public void addParameter(Parameter p) {
            parameters.add(p);
        }

        public List<Parameter> getParameters() {
            return parameters;
        }

        @Override
        public void print(Appendable writer, int indentation) throws IOException {
            writer.append(Util.duplicate("  ", indentation) +
                command.getText());
            for (Parameter p : parameters) {
                writer.append(" ");
                p.print(writer, indentation);
            }
            writer.append(";");
        }

        public ProofNode getProofNode() {
            return proofNode;
        }

        public void setProofNode(ProofNode proofNode) {
            this.proofNode = proofNode;
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

        @Override
        public void print(Appendable writer, int indentation) throws IOException {
            writer.append(name.getText() + "=" + value.getText());
        }
    }

    public static class Cases extends Statement {
        private List<Case> cases = new LinkedList<>();

        public void addCase(Case cas) {
            cases.add(cas);
        }

        public List<Case> getCases() {
            return cases;
        }

        @Override
        public void print(Appendable writer, int indentation) throws IOException {
            writer.append(Util.duplicate("  ", indentation) + "cases {");
            for (Case cas : cases) {
                writer.append("\n");
                cas.print(writer, indentation);
            }
            writer.append("\n" + Util.duplicate("  ", indentation) + "}");
        }
    }

    public static class Case extends ScriptAST {
        private Token label;
        private List<Statement> statements = new LinkedList<>();
        private ProofNode proofNode;

        public void setLabel(Token label) {
            this.label = label;
        }

        public Token getLabel() {
            return label;
        }

        public void addStatement(Statement stmt) {
            statements.add(stmt);
        }

        public void addStatements(Collection<? extends Statement> stmts) {
            statements.addAll(stmts);
        }

        public <R> void visit(FunctionWithException<Command, R, ScriptException> commandFct,
                              FunctionWithException<Cases, R, ScriptException> casesFct) throws ScriptException {
            for (Statement statement : statements) {
                statement.visit(commandFct, casesFct);
            }
        }

        public List<Statement> getStatements() {
            return statements;
        }

        @Override
        public void print(Appendable writer, int indentation) throws IOException {
            indentation ++;
            writer.append(Util.duplicate("  ", indentation) + label.getText() + ":");
            indentation ++;
            for (Statement statement : statements) {
                writer.append("\n");
                statement.print(writer, indentation);
            }
        }

        public void setProofNode(ProofNode node) {
            this.proofNode = node;
        }

        public ProofNode getProofNode() {
            return proofNode;
        }
    }


}
