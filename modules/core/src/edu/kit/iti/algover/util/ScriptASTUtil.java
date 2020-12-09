package edu.kit.iti.algover.util;

import edu.kit.iti.algover.nuscript.ScriptAST;
import edu.kit.iti.algover.nuscript.ScriptAST.Script;
import edu.kit.iti.algover.nuscript.ScriptAST.Statement;
import edu.kit.iti.algover.nuscript.ScriptAST.Cases;
import edu.kit.iti.algover.nuscript.ScriptAST.Case;
import edu.kit.iti.algover.nuscript.ScriptAST.Command;


import javax.swing.plaf.nimbus.State;
import java.util.List;

public class ScriptASTUtil {

    private ScriptASTUtil() {
        throw new Error();
    }

    public static Script createScriptWithStatements(List<Statement> statements) {
        Script script = new Script();

        for (Statement stmt: statements) {
            script.addStatement(stmt);
        }

        return script;
    }

    public static Script insertAfter(Script script, Statement newStatement, Statement target) {
        Script updatedScript = new Script();
        boolean found = false;

        for (Statement statement: script.getStatements()) {
            if (statement == target) {
                // TODO: insert and copy old script
                // if (stmt instanceof Cases), maybe forbid insertion

                updatedScript.addStatement(statement);
                updatedScript.addStatement(newStatement);

            } else {
                Statement insert = statement.visit(command -> command,
                        cases -> ScriptASTUtil.visitCases(cases, newStatement, target));
                updatedScript.addStatement(insert);
            }


        }

        return updatedScript;
    }

    private static Case findAndInsertInCase(Case c, Statement newStatement, Statement target) {
        Case updatedCase = new Case();
        boolean found = false;

        for (Statement statement: c.getStatements()) {
            if (statement == target) {
                found = true;
                // TODO : insert and return
                // if (stmt instanceof Cases), maybe forbid insertion

                updatedCase.addStatement(statement);
                updatedCase.addStatement(newStatement);

            } else {
                Statement insert = statement.visit(command -> command,
                        cases -> ScriptASTUtil.visitCases(cases, newStatement, target));
                updatedCase.addStatement(insert);
            }
        }

        return found ? updatedCase : null;
    }

    private static Statement visitCases(Cases cases, Statement newStatement, Statement target) {
        Cases newCases = new Cases();
        for (Case c : cases.getCases()) {
            Case newCase = ScriptASTUtil.findAndInsertInCase(c, newStatement, target);
            if (newCase != null) {
                // TODO: found and done. Copy rest of AST.
                newCases.addCase(newCase);
            } else {
                newCases.addCase(c);
            }
        }
        return newCases;
    }
}
