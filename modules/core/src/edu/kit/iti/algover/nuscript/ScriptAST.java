/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 *
 */

package edu.kit.iti.algover.nuscript;

import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.util.Conditional;
import edu.kit.iti.algover.util.FunctionWithException;
import edu.kit.iti.algover.util.Util;
import org.antlr.v4.runtime.ParserRuleContext;
import org.antlr.v4.runtime.Token;

import java.io.IOException;
import java.util.ArrayList;
import java.util.Collection;
import java.util.LinkedList;
import java.util.List;
import java.util.Objects;

/**
 * This class is the base class for the abstract syntax tree of the new script parser.
 *
 * There are: entire scripts, commands, parameters cases-statements, a single case,
 *
 * @author Mattias Ulbrich
 *
 * remark from Valentin Springsklee: Maybe introduce common super type only for Script and Case,
 * (which is again subtype of ScriptAST). Something like Container. Should define a list of
 * statements.
 *
 */
public abstract class ScriptAST {

    /** The first token of this AST elements */
    private Token begin;

    /** The last token of this AST elements */
    private Token end;

    /**
     * Extract the beginning and end of this AST from a parsing context.
     * @param ctx the non-null rule context to extract from
     */
    public void setRangeFrom(ParserRuleContext ctx) {
        this.begin = ctx.start;
        this.end = ctx.stop;
    }

    /**
     * The the first token of this AST
     * @return the non-null first token
     */
    public Token getBeginToken() {
        return begin;
    }

    /**
     * The the last token of this AST
     * @return the non-null first token
     */
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

    /**
     * Print the AST (such that it can be parsed again) to a writer
     * @param writer a non-null object to write to
     * @param indentation the level of indentation for the spaces in the line
     * @throws IOException if writing fails
     */
    public abstract void print(Appendable writer, int indentation) throws IOException;

    /**
     * This class captures an entire script -- which is essentially a list of statements.
     */
    public static final class Script extends ScriptAST {

        /** The sequence of statements in the script */
        private final List<Statement> statements = new LinkedList<>();

        public List<Statement> getStatements() {
            return statements;
        }

        /**
         * Ad a single statement to the list of statements.
         *
         * @param stmt, a non-null statement
         */
        public void addStatement(Statement stmt) {
            statements.add(stmt);
        }

        /**
         * run a visitation on all statements of the script in natural order.
         *
         * @param commandFct the function to apply to all {@link Command} objects.
         * @param casesFct the function to apply to all {@link Cases} objects.
         * @param <R> the result type of the functions
         * @param <Ex> the result that may be thrown by the functions
         */
        public <R, Ex extends Exception> void visit(FunctionWithException<Command, R, Ex> commandFct,
                FunctionWithException<Cases, R, Ex> casesFct) throws Ex {
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

    /**
     * This abstract class captures a single statement: either a command or a "cases".
     */
    public abstract static class Statement extends ScriptAST {

        /**
         * A poor man's version of a visitor which takes two functions that react to
         * commands and cases respectively.
         *
         * Should there be more statement types in the future, consider using a proper visitor.
         *
         * @param commandFct the function to apply to a {@link Command} object.
         * @param casesFct the function to apply to a {@link Cases} object.
         * @param <R> the result type of the function
         * @param <Ex> the result that may be thrown by the function
         */
        public abstract <R, Ex extends Exception> R visit(
                FunctionWithException<Command, R, Ex> commandFct,
                FunctionWithException<Cases, R, Ex> casesFct) throws Ex;

    }

    /**
     * This class captures a single command: command name and parameters.
     */
    public static final class Command extends Statement {

        /** The actual command name token */
        private Token command;

        private ByClause byClause;

        /** The list of all parameters to the command */
        private final List<Parameter> parameters = new ArrayList<>();

        /** A pointer to the proof node to which this command is applied */
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
            if (byClause == null) {
                writer.append(";");
            } else {
                byClause.print(writer, indentation);
            }
        }

        /**
         * Return the proof node to which this command is applied
         * @return a pointer into the proof to which this AST refers.
         */
        public ProofNode getProofNode() {
            return proofNode;
        }

        public void setProofNode(ProofNode proofNode) {
            this.proofNode = proofNode;
        }

        @Override
        public <R, Ex extends Exception> R
                visit(FunctionWithException<Command, R, Ex> commandFct,
                      FunctionWithException<Cases, R, Ex> casesFct) throws Ex {
            return commandFct.apply(this);
        }

        public ByClause getByClause() {
            return byClause;
        }

        public void setByClause(ByClause byClause) {
            this.byClause = byClause;
        }
    }

    /**
     * This class captures a single parameter to a command. Consists of a name and a value.
     * The value type can differ.
     */
    public static final class Parameter extends ScriptAST {

        /** The name of the parameter. This may be null if ommitted in the script! */
        private Token name;

        /** The value assigned to the parameter. Not null. The
         * type of the token may be divers.
         */
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
            if (name != null) {
                writer.append(name.getText()).append("=");
            }
            writer.append(value.getText());
        }
    }

    /**
     * This class captures a cases statements which essentially consists
     * of a collection of {@link Case} objects.
     */
    public static final class Cases extends Statement {
        private final List<Case> cases = new LinkedList<>();

        public void addCase(Case cas) {
            cases.add(cas);
        }

        public List<Case> getCases() {
            return cases;
        }

        @Override
        public void print(Appendable writer, int indentation) throws IOException {
            writer.append(Util.duplicate("  ", indentation)).append("cases {");
            for (Case cas : cases) {
                writer.append("\n");
                cas.print(writer, indentation);
            }
            writer.append("\n").append(Util.duplicate("  ", indentation)).append("}");
        }

        @Override
        public <R, Ex extends Exception> R
                visit(FunctionWithException<Command, R, Ex> commandFct,
                      FunctionWithException<Cases, R, Ex> casesFct) throws Ex {
            return casesFct.apply(this);
        }
    }

    /**
     * This class captures a single case in a cases statements.
     * This is comprised by a set of statements.
     */
    public static final class Case extends ScriptAST {
        /** The label of the case of type STRING_LITERAL */
        private Token label;

        /** The list of statements of this case */
        private final List<Statement> statements = new LinkedList<>();

        /** The node to which the head of the case points */
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
            writer.append(Util.duplicate("  ", indentation)).
                   append(label.getText()).append(":");
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

    /**
     * This class captures a single case in a cases statements.
     * This is comprised by a set of statements.
     */
    public static final class ByClause extends ScriptAST {

        /** The list of statements of this clause */
        private final List<Statement> statements = new LinkedList<>();

        /** If there is a '{', let's remember that for highlighting. */
        private Token openingBrace = null;

        /** The node to which the head of the case points */
        private ProofNode proofNode;

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

        @Override
        public void print(Appendable writer, int indentation) throws IOException {
            writer.append(" by ");
            if (statements.size() == 1) {
                statements.get(0).print(writer, 0);
            } else {
                writer.append("{");
                indentation ++;
                for (Statement statement : statements) {
                    writer.append("\n");
                    statement.print(writer, indentation);
                }
                indentation --;
                writer.append("\n").
                        append(Util.duplicate("  ", indentation)).
                        append("}");
            }
        }

        public List<Statement> getStatements() {
            return statements;
        }

        public Token getOpeningBrace() {
            return openingBrace;
        }

        public void setOpeningBrace(Token openingBrace) {
            this.openingBrace = openingBrace;
        }

        public ProofNode getProofNode() {
            return proofNode;
        }
    }

}
