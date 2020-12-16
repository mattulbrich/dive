package edu.kit.iti.algover.nuscript;

import edu.kit.iti.algover.nuscript.ScriptAST.ByClause;
import edu.kit.iti.algover.nuscript.ScriptAST.Case;
import edu.kit.iti.algover.nuscript.ScriptAST.Cases;
import edu.kit.iti.algover.nuscript.ScriptAST.Command;
import edu.kit.iti.algover.nuscript.ScriptAST.Parameter;
import edu.kit.iti.algover.nuscript.ScriptAST.Script;

public interface ScriptASTVisitor<A, R, Ex extends Exception> {
    R visitScript(Script script, A arg) throws Ex;

    R visitCommand(Command command, A arg) throws Ex;

    R visitParameter(Parameter parameter, A arg) throws Ex;

    R visitCases(Cases cases, A arg) throws Ex;

    R visitCase(Case aCase, A arg) throws Ex;

    R visitByClause(ByClause byClause, A arg) throws Ex;
}
