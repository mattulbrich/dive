/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 *
 */

package edu.kit.iti.algover.nuscript.parser;

import edu.kit.iti.algover.nuscript.ScriptAST;
import edu.kit.iti.algover.nuscript.ScriptAST.ByClause;
import edu.kit.iti.algover.nuscript.ScriptAST.Case;
import edu.kit.iti.algover.nuscript.ScriptAST.Cases;
import edu.kit.iti.algover.nuscript.ScriptAST.Command;
import edu.kit.iti.algover.nuscript.ScriptAST.Parameter;
import edu.kit.iti.algover.nuscript.ScriptAST.Script;
import edu.kit.iti.algover.nuscript.ScriptAST.Statement;
import edu.kit.iti.algover.nuscript.parser.ScriptParser.ByClauseContext;
import edu.kit.iti.algover.nuscript.parser.ScriptParser.CasesStmtContext;
import edu.kit.iti.algover.nuscript.parser.ScriptParser.CommandStmtContext;
import edu.kit.iti.algover.nuscript.parser.ScriptParser.ParameterContext;
import edu.kit.iti.algover.nuscript.parser.ScriptParser.ScriptContext;
import edu.kit.iti.algover.nuscript.parser.ScriptParser.SingleCaseContext;
import edu.kit.iti.algover.nuscript.parser.ScriptParser.StatementContext;
import org.antlr.v4.runtime.CommonToken;
import org.antlr.v4.runtime.tree.ParseTreeVisitor;

/**
 * A visitor that translates a concrete parser syntax tree to an abstract syntax tree.
 *
 * @author Mattias Ulbrich
 */
public class ASTVisitor extends ScriptBaseVisitor<ScriptAST> {
    @Override
    public Script visitScript(ScriptContext ctx) {
        Script result = new Script();
        for (StatementContext stm : ctx.statement()) {
            result.addStatement((Statement) stm.accept(this));
        }
        result.setRangeFrom(ctx);
        return result;
    }

    @Override
    public ScriptAST visitCommandStmt(CommandStmtContext ctx) {
        Command result = new Command();
        result.setCommand(ctx.cmd);
        int unnamedCounter = 1;
        for (ParameterContext p : ctx.parameter()) {
            Parameter parameter = (Parameter) p.accept(this);
//            if (parameter.getName() == null) {
//                parameter.setName(new CommonToken(ScriptLexer.ID, "#" + unnamedCounter));
//                unnamedCounter ++;
//            }
            result.addParameter(parameter);

        }
        result.setRangeFrom(ctx);
        if (ctx.byClause() != null) {
            result.setByClause(visitByClause(ctx.byClause()));
        }
        return result;
    }

    @Override
    public ScriptAST visitCasesStmt(CasesStmtContext ctx) {
        Cases result = new Cases();
        for (SingleCaseContext cas : ctx.singleCase()) {
            result.addCase((Case)cas.accept(this));
        }
        result.setRangeFrom(ctx);
        return result;
    }

    @Override
    public ScriptAST visitSingleCase(SingleCaseContext ctx) {
        Case result = new Case();
        result.setLabel(ctx.label);
        for (StatementContext stm : ctx.statement()) {
            result.addStatement((Statement) stm.accept(this));
        }
        result.setRangeFrom(ctx);
        return result;
    }

    @Override
    public ScriptAST visitParameter(ParameterContext ctx) {
        Parameter result = new Parameter();
        result.setName(ctx.pname);
        result.setValue(ctx.expr.start);
        result.setRangeFrom(ctx);
        return result;
    }

    @Override
    public ByClause visitByClause(ByClauseContext ctx) {
        ByClause result = new ByClause();
        result.setRangeFrom(ctx);
        result.setOpeningBrace(ctx.BEGIN().getSymbol());
        if (ctx.commandStmt() != null) {
            result.addStatement((Statement)ctx.commandStmt().accept(this));
        } else {
            for (StatementContext stm : ctx.statement()) {
                result.addStatement((Statement)stm.accept(this));
            }
        }
        return result;
    }
}
