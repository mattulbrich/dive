/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 *
 */

package edu.kit.iti.algover.nuscript;

import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.util.sealable.Sealable;
import edu.kit.iti.algover.util.sealable.SealableList;
import edu.kit.iti.algover.util.sealable.SealedException;
import org.antlr.v4.runtime.ParserRuleContext;
import org.antlr.v4.runtime.Token;

import java.io.IOException;
import java.util.ArrayList;
import java.util.Collection;
import java.util.LinkedList;
import java.util.List;
import java.util.Objects;
import java.util.function.Supplier;

/**
 * This class is the base class for the abstract syntax tree of the new script
 * parser.
 *
 * Objects of this class are in
 *
 * There are: entire scripts, commands, parameters cases-statements, a single
 * case,
 *
 * @author Mattias Ulbrich
 */
public abstract class ScriptAST {

    /**
     * an ast can be made an immutable object by setting it sealed.
     * All children nodes must also be sealed.
     * @see #seal()
     * @see #isSealed()
     */
    private boolean sealed = false;

    /**
     * This is used for the {@link edu.kit.iti.algover.util.sealable.Sealable}
     * instances to check for a sealed ast.
     */
    protected final Supplier<Boolean> sealCheck = this::isSealed;

    /** The first token of this AST elements */
    private final Sealable<Token> begin = new Sealable<>(sealCheck);

    /** The last token of this AST elements */
    private final Sealable<Token> end = new Sealable<>(sealCheck);

    /** The script AST element to which this element belongs.
     * null for instances of {@link Script}. */
    private final Sealable<ScriptAST> parent = new Sealable<>(sealCheck);

    /**
     * Extract the beginning and end of this AST from a parsing context.
     * Requires that the ast has not been sealed.
     * @param ctx the non-null rule context to extract from
     * @throws SealedException if this node has been sealed.
     */
    public void setRangeFrom(ParserRuleContext ctx) throws SealedException {
        this.begin.set(ctx.start);
        this.end.set(ctx.stop);
    }

    /**
     * Set the parent node in the AST for this node.
     * Requires that the ast has not been sealed.
     *
     * @param parent null only if this is instance of {@link Script}
     * @throws SealedException if this node has been sealed.
     */
    public void setParent(ScriptAST parent) throws SealedException {
        this.parent.set(parent);
    }

    /**
     * Get the script AST element to which this element belongs.
     * @return null only for instances of {@link Script}
     */
    public ScriptAST getParent() {
        return parent.get();
    }

    /**
     * The the first token of this AST
     * @return the non-null first token
     */
    public Token getBeginToken() {
        return begin.get();
    }

    /**
     * The the last token of this AST
     * @return the non-null first token
     */
    public Token getEndToken() {
        return end.get();
    }

    @Override
    public final String toString() {
        try {
            StringBuilder sb = new StringBuilder();
            this.accept(new PrintVisitor(sb), 0);
            return sb.toString();
        } catch (IOException e) {
            e.printStackTrace();
            return Objects.toString(this);
        }
    }

    /**
     * Seal this ScriptAST and, transitively, all its children.
     * Once sealed, the ast cannot be modified any more.
     * The method may be called more than once.
     *
     * Note: This method does not seal the parent node to which it points!
     */
    public void seal() {
        this.sealed = true;
    }

    /**
     * Find out if this object has  been sealed
     * Once this method returns true, all subsequent calls will return true.
     *
     * @return true iff sealed
     */
    public boolean isSealed() {
        return this.sealed;
    }

    public abstract <A, R, Ex extends Exception>
        R accept(ScriptASTVisitor<A, R, Ex> visitor, A arg) throws Ex;

    /**
     * Obtain a fresh modifiable copy of this AST. It will be a deep tree copy
     * (but tokens and proof nodes are not cloned).
     *
     * This method returns a {@link ScriptAST} object. If you want to avoid
     * casts to a more detailed subtype, consider invoking:
     * <pre>
     *     UnsealedCopyVisitor.INSTANCE.visitScript(script, null);
     * </pre>
     * which returns a {@link Script} object, similarly for other classes.
     *
     * @return a freshly created, not sealed script ast of the same class as
     * this object.
     */
    public ScriptAST mkUnsealedCopy() {
        return accept(UnsealedCopyVisitor.INSTANCE, getParent());
    }

    /**
     * This abstract class has the functionality of retrieving a list of statements.
     */
    public abstract static class StatementList extends ScriptAST {

        /** The sequence of statements in this element */
        private SealableList<Statement> statements =
                new SealableList<>(sealCheck, new LinkedList<>());

        /**
         * Add a statement to the end of the statement list of this element.
         * Requires that this not be sealed.
         *
         * @param stmt non-null statement to add
         * @throws SealedException if the ast has been sealed.
         */
        public void addStatement(Statement stmt) {
            // Valentin: Consider setting parent relationship here
            statements.add(stmt);
        }

        /**
         * Return the list of statement contained in this AST element. If the
         * ast has been sealed, this is an unmodifiable list of sealed ast
         * elements.
         *
         * You may modify the list if this ast node has not been sealed.
         *
         * @return the list of statements of this element.
         */
        public List<Statement> getStatements() {
            return statements;
        }

        /**
         * Add a collection of statements to the end of the statement list of
         * this element. Requires that this not be sealed.
         *
         * @param stmts a non-collection of non-null statements to add
         * @throws SealedException if the ast has been sealed.
         */
        public void addStatements(Collection<? extends Statement> stmts) {
            statements.addAll(stmts);
        }

        /**
         * Replace the statements of this element by the given collection of
         * statements. Requires that this not be sealed.
         *
         * @param stmts a non-collection of non-null statements to replace with.
         * @throws SealedException if the ast has been sealed.
         */
        public void setStatements(Collection<? extends Statement> stmts) {
            statements.clear();
            statements.addAll(stmts);
        }

        @Override
        public void seal() {
            super.seal();
            for (Statement statement : statements) {
                statement.seal();
            }
        }
    }

    /**
     * This class captures an entire script -- which is essentially a list of statements.
     */
    public static final class Script extends StatementList {

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
        private final Sealable<Token> command = new Sealable<>(sealCheck);

        private final Sealable<ByClause> byClause = new Sealable<>(sealCheck);

        /** The list of all parameters to the command */
        private final SealableList<Parameter> parameters =
                new SealableList<>(sealCheck, new ArrayList<>());

        /**
         * A pointer to the proof node to which this command is applied
         */
        private final Sealable<ProofNode> proofNode = new Sealable<>(sealCheck);

        /**
         * Set the command token for this command.
         * Requires that the ast has not been sealed.
         * @param command non-null token to set for the command
         * @throws SealedException if this node has been sealed.
         */
        public void setCommand(Token command) {
            this.command.set(command);
        }

        public Token getCommand() {
            return command.get();
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
            return proofNode.get();
        }

        public void setProofNode(ProofNode proofNode) {
            this.proofNode.set(proofNode);
        }

        public ByClause getByClause() {
            return byClause.get();
        }

        public void setByClause(ByClause byClause) {
            this.byClause.set(byClause);
        }

        @Override
        public void seal() {
            super.seal();
            if(byClause.isSet()) {
                byClause.get().seal();
            }
            for (Parameter parameter : parameters) {
                parameter.seal();
            }
        }

        @Override
        public boolean equals(Object other) {
            if(other instanceof Command) {
                Command o = (Command) other;
                return command == null ? o.command == null : command.equals(o.command) &&
                        byClause == null ? o.byClause == null : byClause.equals(o.byClause) &&
                        parameters == null ? o.parameters == null : parameters.equals(o.parameters) &&
                        proofNode == null ? o.proofNode == null : proofNode.equals(o.proofNode);
            }
            return false;
        }
    }

    /**
     * This class captures a single parameter to a command. Consists of a name and a value.
     * The value type can differ.
     */
    public static final class Parameter extends ScriptAST {

        /** The name of the parameter. This may be null if ommitted in the script! */
        private final Sealable<Token> name = new Sealable<>(sealCheck);

        /** The value assigned to the parameter. Not null. The
         * type of the token may be divers.
         */
        private final Sealable<Token> value = new Sealable<>(sealCheck);

        public void setName(Token name) {
            this.name.set(name);
        }

        public Token getName() {
            return name.get();
        }

        public void setValue(Token value) {
            this.value.set(value);
        }

        public Token getValue() {
            return value.get();
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
        private final SealableList<Case> cases =
                new SealableList<>(sealCheck, new LinkedList<>());

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

        @Override
        public void seal() {
            super.seal();
            for (Case aCase : cases) {
                aCase.seal();
            }
        }
    }

    /**
     * This class captures a single case in a cases statements.
     * This is comprised by a set of statements.
     */
    public static final class Case extends StatementList {
        /** The label of the case of type STRING_LITERAL */
        private final Sealable<Token> label = new Sealable<>(sealCheck);

        /** The node to which the head of the case points */
        private final Sealable<ProofNode> proofNode = new Sealable<>(sealCheck);

        public void setLabel(Token label) {
            this.label.set(label);
        }

        public Token getLabel() {
            return label.get();
        }

        @Override
        public <A, R, Ex extends Exception> R accept(ScriptASTVisitor<A, R, Ex> visitor, A arg) throws Ex {
            return visitor.visitCase(this, arg);
        }

        public void setProofNode(ProofNode node) {
            this.proofNode.set(node);
        }

        public ProofNode getProofNode() {
            return proofNode.get();
        }
    }

    /**
     * This class captures a single case in a cases statements.
     * It comprises a set of statements.
     */
    public static final class ByClause extends StatementList {

        /** If there is a '{', let's remember that for highlighting. */
        private final Sealable<Token> openingBrace = new Sealable<>(sealCheck);

        /** The node to which the head of the case points */
        private final Sealable<ProofNode> proofNode = new Sealable<>(sealCheck);

        @Override
        public <A, R, Ex extends Exception> R accept(ScriptASTVisitor<A, R, Ex> visitor, A arg) throws Ex {
            return visitor.visitByClause(this, arg);
        }

        public Token getOpeningBrace() {
            return openingBrace.get();
        }

        public void setOpeningBrace(Token openingBrace) {
            this.openingBrace.set(openingBrace);
        }

        public ProofNode getProofNode() {
            return proofNode.get();
        }
    }

}
