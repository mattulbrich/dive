package edu.kit.iti.algover.rule.script;

import de.uka.ilkd.pp.NoExceptions;
import edu.kit.iti.algover.nuscript.DefaultScriptASTVisitor;
import edu.kit.iti.algover.nuscript.ScriptAST;

public class NavigateUpVisitor extends DefaultScriptASTVisitor<ScriptAST, ScriptAST, NoExceptions> {

    public static NavigateUpVisitor INSTANCE = new NavigateUpVisitor();

    private ScriptAST moveUpFromStatement(ScriptAST.Statement stmt) {
        ScriptAST.StatementList parent = (ScriptAST.StatementList) stmt.getParent();
        int idx = parent.getStatements().indexOf(stmt);
        if (idx > 0) {
            return parent.getStatements().get(idx - 1);
        } else if (idx == 0) {
            if (parent.getParent() != null) {
                return parent.getParent();
            }
        }
        return stmt;
    }


    @Override
    public ScriptAST visitScript(ScriptAST.Script script, ScriptAST arg) throws NoExceptions {
        int numStatements = script.getStatements().size();
        if (numStatements > 0) {
            return script.getStatements().get(numStatements - 1);
        }
        return script;
    }

    @Override
    public ScriptAST visitCase(ScriptAST.Case aCase, ScriptAST arg) throws NoExceptions {
        int numStatements = aCase.getStatements().size();
        if (numStatements > 0) {
            return aCase.getStatements().get(numStatements - 1);
        } else {
            return aCase.getParent();
        }
    }

    @Override
    public ScriptAST visitCases(ScriptAST.Cases cases, ScriptAST arg) throws NoExceptions {
        return moveUpFromStatement(cases);
    }

    @Override
    public ScriptAST visitCommand(ScriptAST.Command command, ScriptAST arg) throws NoExceptions {
        return moveUpFromStatement(command);
    }
}
