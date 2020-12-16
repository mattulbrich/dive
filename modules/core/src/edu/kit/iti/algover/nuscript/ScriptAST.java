/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 *
 */

package edu.kit.iti.algover.nuscript;

import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.util.Conditional;
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
 */
public abstract class ScriptAST {

    /** The first token of this AST elements */
    private Token begin;

    /** The last token of this AST elements */
    private Token end;

    /** The script AST element to which this element belongs.
     * null for instances of {@link Script}. */
    private ScriptAST parent;

    /**
     * Extract the beginning and end of this AST from a parsing context.
     * @param ctx the non-null rule context to extract from
     */
    public void setRangeFrom(ParserRuleContext ctx) {
        this.begin = ctx.start;
        this.end = ctx.stop;
    }

    /**
     * Set the parent node in the AST for this node.
     * @param parent, only null if this is instance of {@link Script}
     */
    public void setParent(ScriptAST parent) {
        this.parent = parent;
    }

    /** Get the script AST element to which this element belongs.
     * @return null only for instances of {@link Script}
     */
    public ScriptAST getParent() {
        return parent;
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
        try {
            StringBuilder sb = new StringBuilder();
            this.accept(new PrintVisitor(sb), 0);
            return sb.toString();
        } catch (IOException e) {
            e.printStackTrace();
            return Objects.toString(this);
        }
    }

    public abstract <A, R, Ex extends Exception>
        R accept(ScriptASTVisitor<A, R, Ex> visitor, A arg) throws Ex;


    /**
     * This abstract class has the functionality of retrieving a list of statements.
     */
    public static abstract class StatementList extends ScriptAST {
        /**
         * Return the list of statement contained in this AST element
         * @return the internal list of statements; do not modify
         */
        public abstract List<Statement> getStatements();
    }

    /**
     * This class captures an entire script -- which is essentially a list of statements.
     */
    public static final class Script extends StatementList {

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

        public <A, R, Ex extends Exception> R accept(ScriptASTVisitor<A, R, Ex> visitor, A arg) throws Ex {
            return visitor.visitScript(this, arg);
        }

    }

    /**
     * This abstract class captures a single statement: either a command or a "cases".
     */
    public abstract static class Statement extends ScriptAST {
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
        public <A, R, Ex extends Exception> R accept(ScriptASTVisitor<A, R, Ex> visitor, A arg) throws Ex {
            return visitor.visitCommand(this, arg);
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
        public <A, R, Ex extends Exception> R accept(ScriptASTVisitor<A, R, Ex> visitor, A arg) throws Ex {
            return visitor.visitParameter(this, arg);
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
        public <A, R, Ex extends Exception> R accept(ScriptASTVisitor<A, R, Ex> visitor, A arg) throws Ex {
            return  visitor.visitCases(this, arg);
        }
    }

    /**
     * This class captures a single case in a cases statements.
     * This is comprised by a set of statements.
     */
    public static final class Case extends StatementList {
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

        public List<Statement> getStatements() {
            return statements;
        }

        @Override
        public <A, R, Ex extends Exception> R accept(ScriptASTVisitor<A, R, Ex> visitor, A arg) throws Ex {
            return visitor.visitCase(this, arg);
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
     * It comprises a set of statements.
     */
    public static final class ByClause extends StatementList {

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

        @Override
        public <A, R, Ex extends Exception> R accept(ScriptASTVisitor<A, R, Ex> visitor, A arg) throws Ex {
            return visitor.visitByClause(this, arg);
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
