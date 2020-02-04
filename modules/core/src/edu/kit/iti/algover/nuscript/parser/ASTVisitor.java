/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 *
 */

package edu.kit.iti.algover.nuscript.parser;

import edu.kit.iti.algover.nuscript.ast.ScriptAST;
import edu.kit.iti.algover.nuscript.ast.ScriptAST.Case;
import edu.kit.iti.algover.nuscript.ast.ScriptAST.Cases;
import edu.kit.iti.algover.nuscript.ast.ScriptAST.Command;
import edu.kit.iti.algover.nuscript.ast.ScriptAST.Parameter;
import edu.kit.iti.algover.nuscript.ast.ScriptAST.Script;
import edu.kit.iti.algover.nuscript.parser.ScriptParser.CasesStmtContext;
import edu.kit.iti.algover.nuscript.parser.ScriptParser.CommandStmtContext;
import edu.kit.iti.algover.nuscript.parser.ScriptParser.ParameterContext;
import edu.kit.iti.algover.nuscript.parser.ScriptParser.ScriptContext;
import edu.kit.iti.algover.nuscript.parser.ScriptParser.SingleCaseContext;
import edu.kit.iti.algover.nuscript.parser.ScriptParser.StatementContext;

public class ASTVisitor extends ScriptBaseVisitor<ScriptAST> {
    @Override
    public Script visitScript(ScriptContext ctx) {
        Script result = new Script();
        for (StatementContext stm : ctx.statement()) {
            result.addStatement((Command) stm.accept(this));
        }
        return result;
    }

    @Override
    public ScriptAST visitCommandStmt(CommandStmtContext ctx) {
        Command result = new Command();
        result.setCommand(ctx.cmd);
        for (ParameterContext p : ctx.parameter()) {
            result.addParameter((Parameter)p.accept(this));
        }
        return result;
    }

    @Override
    public ScriptAST visitCasesStmt(CasesStmtContext ctx) {
        Cases cases = new Cases();
        for (SingleCaseContext cas : ctx.singleCase()) {
            cases.addCase((Case)cas.accept(this));
        }
        return cases;
    }

    @Override
    public ScriptAST visitSingleCase(SingleCaseContext ctx) {
        Case result = new Case();
        result.setLabel(ctx.label);
        for (StatementContext stm : ctx.statement()) {
            result.addStatement((Command) stm.accept(this));
        }
        return result;
    }

    @Override
    public ScriptAST visitParameter(ParameterContext ctx) {
        Parameter p = new Parameter();
        p.setName(ctx.pname);
        p.setValue(ctx.expr.start);
        return p;
    }
}
