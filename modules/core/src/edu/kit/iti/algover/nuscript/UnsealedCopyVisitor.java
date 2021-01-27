package edu.kit.iti.algover.nuscript;

import de.uka.ilkd.pp.NoExceptions;
import edu.kit.iti.algover.nuscript.ScriptAST.ByClause;
import edu.kit.iti.algover.nuscript.ScriptAST.Case;
import edu.kit.iti.algover.nuscript.ScriptAST.Cases;
import edu.kit.iti.algover.nuscript.ScriptAST.Command;
import edu.kit.iti.algover.nuscript.ScriptAST.Parameter;
import edu.kit.iti.algover.nuscript.ScriptAST.Script;
import edu.kit.iti.algover.nuscript.ScriptAST.Statement;

public class UnsealedCopyVisitor extends DefaultScriptASTVisitor<ScriptAST, ScriptAST, NoExceptions> {

    public static final UnsealedCopyVisitor INSTANCE = new UnsealedCopyVisitor();

    @Override
    public Script visitScript(Script script, ScriptAST arg) throws NoExceptions {
        Script ret = new Script();
        for (Statement statement : script.getStatements()) {
            ret.addStatement((Statement)statement.accept(this, arg));
        }
        ret.setParent(arg);
        return ret;
    }

    @Override
    public Parameter visitParameter(Parameter parameter, ScriptAST arg) throws NoExceptions {
        Parameter ret = new Parameter();
        ret.setName(parameter.getName());
        ret.setValue(parameter.getValue());
        ret.setParent(arg);
        return ret;
    }

    @Override
    public ScriptAST visitCommand(Command command, ScriptAST arg) throws NoExceptions {
        Command ret = new Command();
        ret.setCommand(command.getCommand());
        ret.setByClause(visitByClause(command.getByClause(), ret));
        ret.setProofNode(command.getProofNode());
        for (Parameter parameter : command.getParameters()) {
            ret.addParameter(visitParameter(parameter, ret));
        }
        ret.setParent(arg);
        return ret;
    }

    @Override
    public ByClause visitByClause(ByClause byClause, ScriptAST arg) throws NoExceptions {
        ByClause ret = new ByClause();
        ret.setOpeningBrace(byClause.getOpeningBrace());
        for (Statement statement : byClause.getStatements()) {
            ret.addStatement((Statement)statement.accept(this, ret));
        }
        ret.setParent(arg);
        return ret;
    }

    @Override
    public Case visitCase(Case aCase, ScriptAST arg) throws NoExceptions {
        Case ret = new Case();
        aCase.setLabel(aCase.getLabel());
        for (Statement statement : aCase.getStatements()) {
            ret.addStatement((Statement)statement.accept(this, ret));
        }
        ret.setProofNode(aCase.getProofNode());
        ret.setParent(arg);
        return ret;
    }

    @Override
    public Cases visitCases(Cases cases, ScriptAST arg) throws NoExceptions {
        Cases ret = new Cases();
        for (Case aCase : cases.getCases()) {
            ret.addCase(visitCase(aCase, ret));
        }
        return ret;
    }
}
