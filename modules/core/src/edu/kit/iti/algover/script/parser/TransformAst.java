/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.script.parser;

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
import edu.kit.iti.algover.script.ScriptLanguageVisitor;
import edu.kit.iti.algover.script.ast.*;
import org.antlr.v4.runtime.ParserRuleContext;
import org.antlr.v4.runtime.tree.ErrorNode;
import org.antlr.v4.runtime.tree.ParseTree;
import org.antlr.v4.runtime.tree.RuleNode;
import org.antlr.v4.runtime.tree.TerminalNode;

import java.util.List;

/**
 * @author Alexander Weigl
 * @version 1 (27.04.17)
 */

// REVIEW: Add the missing generic parameters! Please!

//@SuppressWarnings({"unchecked", "rawtypes"})
public class TransformAst implements ScriptLanguageVisitor<Object> {
    //private List<ProofScript> scripts = new ArrayList<>(10);

    /*public List<ProofScript> getScripts() {
        return scripts;
    }*/
    private ProofScript script;

    public ProofScript getScript() {
        return script;
    }

    @Override
    public ProofScript visitScript(ScriptLanguageParser.ScriptContext ctx) {
        ProofScript s = new ProofScript();

        if (ctx.name != null) {
            s.setName(ctx.name.getText());
            s.setNamedScript(true);
        } else {
            s.setName("");
        }
        s.setRuleContext(ctx);

        if (ctx.signature != null)
            s.setSignature((Signature) ctx.signature.accept(this));
        s.setBody((Statements) ctx.body.accept(this));
        return s;
    }

    @Override
    public ProofScript visitStart(ScriptLanguageParser.StartContext ctx) {
        ProofScript s = (ProofScript) ctx.script().accept(this);
        //ctx.script().forEach(s ->
        //        scripts.add((ProofScript) s.accept(this)));
        script = s;
        return s;
    }


    @Override
    public Signature visitArgList(ScriptLanguageParser.ArgListContext ctx) {
        Signature signature = new Signature();
        for (ScriptLanguageParser.VarDeclContext decl : ctx.varDecl()) {
            signature.put(new Variable(decl.name), Type.findType(decl.type.getText()));
        }
        return signature;
    }

    /**
     * @param ctx the parse tree
     * @return
     * Will be deprecated not needed, handled in {@link #visitArgList(ScriptLanguageParser.ArgListContext)}
     */
    @Override
    public Object visitVarDecl(ScriptLanguageParser.VarDeclContext ctx) {
       /* VariableDeclaration varDecl = new VariableDeclaration();
        varDecl.setIdentifier(new Variable(ctx.name));
        varDecl.setType(Type.findType(ctx.type.getText()));
        return varDecl;*/
        return null;

    }

    @Override
    public Statements visitStmtList(ScriptLanguageParser.StmtListContext ctx) {
        Statements statements = new Statements();
        for (ScriptLanguageParser.StatementContext stmt : ctx.statement()) {
            statements.add((Statement) stmt.accept(this));
        }
        return statements;
    }


    @Override
    public Object visitStatement(ScriptLanguageParser.StatementContext ctx) {
        return ctx.getChild(0).accept(this);
    }

    @Override
    public Object visitAssignment(ScriptLanguageParser.AssignmentContext ctx) {
        AssignmentStatement assign = new AssignmentStatement();
        assign.setRuleContext(ctx);
        assign.setLhs(new Variable(ctx.variable));
        if (ctx.type != null) {
            assign.setType(Type.findType(ctx.type.getText()));
        }
        if (ctx.expression() != null) {
            assign.setRhs((Expression) ctx.expression().accept(this));
        }
        return assign;
    }

    @Override
    public BinaryExpression visitExprMultiplication(ScriptLanguageParser.ExprMultiplicationContext ctx) {
        return createBinaryExpression(ctx, ctx.expression(), Operator.MULTIPLY);
    }

    private BinaryExpression createBinaryExpression(ParserRuleContext ctx,
                                                    List<ScriptLanguageParser.ExpressionContext> expression, Operator op) {
        BinaryExpression be = new BinaryExpression();
        be.setLeft((Expression) expression.get(0).accept(this));
        be.setRight((Expression) expression.get(1).accept(this));
        be.setOperator(op);
        return be;
    }

    private UnaryExpression createUnaryExpression(ParserRuleContext ctx, ScriptLanguageParser.ExpressionContext expression, Operator op) {
        UnaryExpression ue = new UnaryExpression();
        ue.setRuleContext(ctx);
        ue.setExpression((Expression) expression.accept(this));
        ue.setOperator(op);
        return ue;
    }

    @Override
    public Object visitExprNegate(ScriptLanguageParser.ExprNegateContext ctx) {
        return createUnaryExpression(ctx, ctx.expression(), Operator.NEGATE);
    }

    @Override
    public Object visitExprNot(ScriptLanguageParser.ExprNotContext ctx) {
        return createUnaryExpression(ctx, ctx.expression(), Operator.NOT);
    }

    @Override
    public Object visitExprComparison(ScriptLanguageParser.ExprComparisonContext ctx) {
        return createBinaryExpression(ctx, ctx.expression(), findOperator(ctx.op.getText()));
    }


    private Operator findOperator(String n) {
        return findOperator(n, 2);
    }

    private Operator findOperator(String n, int arity) {
        for (Operator op : Operator.values()) {
            if (op.symbol().equals(n) && op.arity() == arity)
                return op;
        }
        throw new IllegalStateException("Operator " + n + " not defined");
    }

    @Override
    public Object visitExprEquality(ScriptLanguageParser.ExprEqualityContext ctx) {
        return createBinaryExpression(ctx, ctx.expression(), findOperator(ctx.op.getText()));

    }

    @Override
    public Object visitExprMatch(ScriptLanguageParser.ExprMatchContext ctx) {
        return ctx.matchPattern().accept(this);
    }

    @Override
    public Object visitExprIMP(ScriptLanguageParser.ExprIMPContext ctx) {
        return createBinaryExpression(ctx, ctx.expression(), Operator.IMPLICATION);

    }

    @Override
    public Object visitExprParen(ScriptLanguageParser.ExprParenContext ctx) {
        return ctx.expression().accept(this);
    }

    @Override
    public Object visitExprOr(ScriptLanguageParser.ExprOrContext ctx) {
        return createBinaryExpression(ctx, ctx.expression(), Operator.OR);

    }

    @Override
    public Object visitExprLineOperators(ScriptLanguageParser.ExprLineOperatorsContext ctx) {
        return createBinaryExpression(ctx, ctx.expression(), findOperator(ctx.op.getText()));

    }

    @Override
    public Object visitExprAnd(ScriptLanguageParser.ExprAndContext ctx) {
        return createBinaryExpression(ctx, ctx.expression(), Operator.AND);

    }

    @Override
    public Object visitExprLiterals(ScriptLanguageParser.ExprLiteralsContext ctx) {
        return ctx.literals().accept(this);
    }

    @Override
    public Object visitExprDivision(ScriptLanguageParser.ExprDivisionContext ctx) {
        return createBinaryExpression(ctx, ctx.expression(), Operator.DIVISION);

    }

    //TODO implement


   /* @Override
    public Object visitExprSubst(ScriptLanguageParser.ExprSubstContext ctx) {
        return null;
    }*/

   /*  @Override
    public Object visitSubstExpressionList(ScriptLanguageParser.SubstExpressionListContext ctx) {
        return null;
    }*/

    @Override
    public Object visitLiteralID(ScriptLanguageParser.LiteralIDContext ctx) {
        return new Variable(ctx.ID().getSymbol());
    }

    @Override
    public Object visitLiteralDigits(ScriptLanguageParser.LiteralDigitsContext ctx) {
        return new IntegerLiteral(ctx.DIGITS().getSymbol());
    }

    @Override
    public Object visitLiteralTerm(ScriptLanguageParser.LiteralTermContext ctx) {
        return new TermLiteral(ctx.getText());
    }

    //TODO create class
    @Override
    public Object visitMatchTermLiteral(ScriptLanguageParser.MatchTermLiteralContext ctx) {
        return new TermLiteral(ctx.getText());
    }

    @Override
    public Object visitSequentLiteral(ScriptLanguageParser.SequentLiteralContext ctx) {
        return new SequentLiteral(ctx.getText());
    }

    @Override
    public Object visitLiteralString(ScriptLanguageParser.LiteralStringContext ctx) {
        return new StringLiteral(ctx.getText());
    }

    @Override
    public Object visitLiteralTrue(ScriptLanguageParser.LiteralTrueContext ctx) {
        return new BooleanLiteral(true, ctx.TRUE().getSymbol());
    }

    @Override
    public Object visitLiteralFalse(ScriptLanguageParser.LiteralFalseContext ctx) {
        return new BooleanLiteral(false, ctx.FALSE().getSymbol());
    }

    @Override
    public Object visitMatchPattern(ScriptLanguageParser.MatchPatternContext ctx) {
        MatchExpression match = new MatchExpression();
        match.setRuleContext(ctx);

        if (ctx.derivable != null) {
            match.setDerivable(true);
            match.setDerivableTerm((Expression) ctx.derivableExpression.accept(this));
        } else {
            if (ctx.argList() != null)
                match.setSignature((Signature) ctx.argList().accept(this));
            match.setPattern((Expression) ctx.pattern.accept(this));
        }

        return match;
    }

    @Override
    public Object visitScriptVar(ScriptLanguageParser.ScriptVarContext ctx) {
        throw new IllegalStateException("not implemented");
    }

  /*  @Override
    public Object visitRepeatStmt(ScriptLanguageParser.RepeatStmtContext ctx) {
        RepeatStatement rs = new RepeatStatement();
        rs.setRuleContext(ctx);
        rs.setBody((Statements) ctx.stmtList().accept(this));
        return rs;
    }*/

    @Override
    public Object visitCasesStmt(ScriptLanguageParser.CasesStmtContext ctx) {
        CasesStatement cases = new CasesStatement();
        ctx.casesList().forEach(c -> cases.getCases().add((CaseStatement) c.accept(this)));
        if (ctx.DEFAULT() != null) {
            cases.setDefaultCase((Statements)
                    ctx.defList.accept(this)
            );
        }
        cases.setRuleContext(ctx);
        return cases;
    }

    @Override
    public Object visitCasesList(ScriptLanguageParser.CasesListContext ctx) {
        //TODO try case
        if (ctx.CLOSES() != null) {
            IsClosableCase isClosableCase = new IsClosableCase();
            isClosableCase.setRuleContext(ctx);
            isClosableCase.setBody((Statements) ctx.bodyScript.accept(this));
            return isClosableCase;
        } else {
            SimpleCaseStatement caseStatement = new SimpleCaseStatement();
            caseStatement.setRuleContext(ctx);
            caseStatement.setGuard((Expression) ctx.expression().accept(this));
            caseStatement.setBody((Statements) ctx.bodyScript.accept(this));
            return caseStatement;
        }
     /*   CaseStatement caseStatement = new CaseStatement();
        caseStatement.setRuleContext(ctx);
        caseStatement.setGuard((Expression) ctx.expression().accept(this));
        caseStatement.setBody((Statements) ctx.stmtList().accept(this));
        return caseStatement;*/

    }

/*
    @Override
    public Object visitSimpleCase(ScriptLanguageParser.SimpleCaseContext ctx) {
        SimpleCaseStatement caseStatement = new SimpleCaseStatement();
        caseStatement.setRuleContext(ctx);
        caseStatement.setGuard((Expression) ctx.expression().accept(this));
        caseStatement.setBody((Statements) ctx.stmtList().accept(this));
        return caseStatement;

    }

    @Override
    public Object visitClosableCase(ScriptLanguageParser.ClosableCaseContext ctx) {
        IsClosableCase isClosableCase = new IsClosableCase();
        isClosableCase.setRuleContext(ctx);
        isClosableCase.setBody((Statements) ctx.stmtList().accept(this));
        return isClosableCase;
    }
*/

    /*  @Override
    public Object visitForEachStmt(ScriptLanguageParser.ForEachStmtContext ctx) {
        ForeachStatement f = new ForeachStatement();
        f.setRuleContext(ctx);
        f.setBody((Statements) ctx.stmtList().accept(this));
        return f;
    }

    @Override
    public Object visitTheOnlyStmt(ScriptLanguageParser.TheOnlyStmtContext ctx) {
        TheOnlyStatement f = new TheOnlyStatement();
        f.setRuleContext(ctx);
        f.setBody((Statements) ctx.stmtList().accept(this));
        return f;
    }*/

    @Override
    public Object visitScriptCommand(ScriptLanguageParser.ScriptCommandContext ctx) {
        CallStatement scs = new CallStatement();
        scs.setRuleContext(ctx);
        scs.setCommand(ctx.cmd.getText());
        if (ctx.parameters() != null) {
            scs.setParameters((Parameters) ctx.parameters().accept(this));
        }
        return scs;
    }

    @Override
    public Object visitParameters(ScriptLanguageParser.ParametersContext ctx) {
        Parameters params = new Parameters();
        int i = 1;
        for (ScriptLanguageParser.ParameterContext pc : ctx.parameter()) {
            Expression expr = (Expression) pc.expr.accept(this);
            Variable key = pc.pname != null ? new Variable(pc.pname) : new Variable("#" + (i++));
            params.put(key, expr);
        }
        return params;
    }

    @Override
    public Object visitParameter(ScriptLanguageParser.ParameterContext ctx) {
        return null;
    }

    @Override
    public Object visit(ParseTree parseTree) {
        throw new IllegalStateException("not implemented");
    }

    @Override
    public Object visitChildren(RuleNode ruleNode) {
        throw new IllegalStateException("not implemented");
    }

    @Override
    public Object visitTerminal(TerminalNode terminalNode) {
        throw new IllegalStateException("not implemented");
    }

    @Override
    public Object visitErrorNode(ErrorNode errorNode) {
        throw new IllegalStateException("not implemented");
    }
}
