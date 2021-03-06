package edu.kit.iti.algover.rule.script;

import de.uka.ilkd.pp.NoExceptions;
import edu.kit.iti.algover.nuscript.DefaultScriptASTVisitor;
import edu.kit.iti.algover.nuscript.ScriptAST;

public class NavigateDownVisitor extends DefaultScriptASTVisitor<ScriptAST, ScriptAST, NoExceptions> {

    public static NavigateDownVisitor INSTANCE = new NavigateDownVisitor();


    @Override
    public ScriptAST visitScript(ScriptAST.Script script, ScriptAST arg) throws NoExceptions {
        return script;
    }

    @Override
    public ScriptAST visitCase(ScriptAST.Case aCase, ScriptAST arg) throws NoExceptions {
        return aCase;
    }

    @Override
    public ScriptAST visitCases(ScriptAST.Cases cases, ScriptAST arg) throws NoExceptions {
        ScriptAST.StatementList parent = (ScriptAST.StatementList) cases.getParent();
        int idx = parent.getStatements().indexOf(cases);
        if (idx >= 0 && idx < parent.getStatements().size() - 1) {
            return parent.getStatements().get(idx + 1);
        } else if (idx == parent.getStatements().size() - 1) {
            return cases.getCases().get(0);
        }
        return cases;
    }

    @Override
    public ScriptAST visitCommand(ScriptAST.Command command, ScriptAST arg) throws NoExceptions {
        ScriptAST.StatementList parent = (ScriptAST.StatementList) command.getParent();
        int idx = parent.getStatements().indexOf(command);
        if (idx >= 0 && idx < parent.getStatements().size() - 1) {
            return parent.getStatements().get(idx + 1);
        } else if (idx == parent.getStatements().size() - 1) {
            return parent;
        }
        return command;
    }
}
