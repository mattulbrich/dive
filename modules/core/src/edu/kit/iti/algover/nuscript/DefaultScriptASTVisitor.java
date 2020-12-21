package edu.kit.iti.algover.nuscript;

import edu.kit.iti.algover.nuscript.ScriptAST.ByClause;
import edu.kit.iti.algover.nuscript.ScriptAST.Case;
import edu.kit.iti.algover.nuscript.ScriptAST.Cases;
import edu.kit.iti.algover.nuscript.ScriptAST.Command;
import edu.kit.iti.algover.nuscript.ScriptAST.Parameter;
import edu.kit.iti.algover.nuscript.ScriptAST.Script;
import edu.kit.iti.algover.nuscript.ScriptAST.Statement;
import edu.kit.iti.algover.nuscript.ScriptAST.StatementList;

public abstract class DefaultScriptASTVisitor<A, R, Ex extends Exception> implements ScriptASTVisitor<A, R, Ex> {

    protected R visitDefault(ScriptAST ast, A arg) throws Ex {
        return null;
    }

    protected void visitStatements(StatementList statementList, A arg) throws Ex {
        for (Statement statement : statementList.getStatements()) {
            statement.accept(this, arg);
        }
    }

    protected void visitCommandChildren(Command command, A arg) throws Ex {
        for (Parameter parameter : command.getParameters()) {
            parameter.accept(this, arg);
        }
        ByClause bc = command.getByClause();
        if (bc != null) {
            bc.accept(this, arg);
        }
    }

    @Override
    public R visitScript(Script script, A arg) throws Ex {
        visitStatements(script, arg);
        return visitDefault(script, arg);
    }

    @Override
    public R visitCommand(Command command, A arg) throws Ex {
        visitCommandChildren(command, arg);
        return visitDefault(command, arg);
    }

    @Override
    public R visitParameter(Parameter parameter, A arg) throws Ex {
        return visitDefault(parameter, arg);
    }

    @Override
    public R visitCases(Cases cases, A arg) throws Ex {
        for (Case aCase : cases.getCases()) {
            aCase.accept(this, arg);
        }
        return visitDefault(cases, arg);
    }

    @Override
    public R visitCase(Case aCase, A arg) throws Ex {
        visitStatements(aCase, arg);
        return visitDefault(aCase, arg);
    }

    @Override
    public R visitByClause(ByClause byClause, A arg) throws Ex {
        visitStatements(byClause, arg);
        return visitDefault(byClause, arg);
    }
}
