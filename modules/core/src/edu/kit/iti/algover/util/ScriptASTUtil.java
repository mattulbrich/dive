package edu.kit.iti.algover.util;

import edu.kit.iti.algover.nuscript.ScriptAST;
import edu.kit.iti.algover.nuscript.ScriptAST.Script;
import edu.kit.iti.algover.nuscript.ScriptAST.Statement;
import edu.kit.iti.algover.nuscript.ScriptAST.Cases;
import edu.kit.iti.algover.nuscript.ScriptAST.Case;
import edu.kit.iti.algover.nuscript.ScriptAST.Command;
import edu.kit.iti.algover.nuscript.parser.ScriptParser;
import edu.kit.iti.algover.proof.ProofNode;
import org.antlr.v4.runtime.CommonToken;


import javax.swing.plaf.nimbus.State;
import java.util.ArrayList;
import java.util.List;
import java.util.logging.Logger;

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

        if (target == null) {
            assert script.getStatements().isEmpty();
            updatedScript.addStatement(newStatement);
            return updatedScript;
        }

        for (Statement statement: script.getStatements()) {
            if (found) {
                updatedScript.addStatement(statement);
                continue;
            }
            if (statement == target) {
                found = true;
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
            if (found) {
                updatedCase.addStatement(statement);
                continue;
            }
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

    /**
     * recursivly inserts all missing case statements in the given script
     *
     * @param pn the proofnode for which the cases should be inserted
     * @param stmts the current script that should be extended by the missing case statements
     * @return a new script containing all necessary case statements
     */
    // MU: Adapted the existing code to nuscript. But it does not seem to be recursive at all.
    // VS: Some Bug for inner cases.
    public static List<ScriptAST.Statement> insertCasesForStatement(ProofNode pn, List<ScriptAST.Statement> stmts) {
        if(stmts.size() == 0) {
            return stmts;
        }
        List<ScriptAST.Statement> result = new ArrayList<>();
        for (int i = 0; i < stmts.size() - 1; ++i) {
            if(stmts.get(i) instanceof ScriptAST.Command) {
                result.add(stmts.get(i));
            } else {
                Logger.getGlobal().warning("Only the last statement may be a cases-statement.");
                return stmts;
            }
            if((pn.getChildren() != null && pn.getChildren().size() == 1)) {
                pn = pn.getChildren().get(0);
            } else if (stmts.size() - 2 != i) {
                Logger.getGlobal().warning("Script has unexpected number of children at some point.");
                return stmts;
            }
        }
        ScriptAST.Statement st = stmts.get(stmts.size() - 1);
        if(pn.getSuccessors().size() == 1 && st instanceof ScriptAST.Command) {
            result.add(st);
        } else if (pn.getChildren().size() > 1 && st instanceof ScriptAST.Cases) {
            result.add(createCasesForNode(pn, ((ScriptAST.Cases) st).getCases()));
        } else if (pn.getChildren().size() > 1 && !(st instanceof ScriptAST.Cases)) {
            result.add(st);
            result.add(createCasesForNode(pn));
        }

        return result;
    }

    /**@
     * Creates all cases for the given proofnode except the ones given in cases
     *
     * @param pn the proofnode for which the cases should be created
     * @param cases the cases that already exist
     * @return a case statement containing all necesarry cases
     */
    private static ScriptAST.Statement createCasesForNode(ProofNode pn, List<ScriptAST.Case> cases) {
        ScriptAST.Cases res = new ScriptAST.Cases();
        for(ProofNode p : pn.getChildren()) {
            boolean found = false;
            for(ScriptAST.Case caze : cases) {
                //apparently some guards are string literals and some are MathcExpressions...
                String caseString = Util.stripQuotes(caze.getLabel().getText());
                if (caseString.equals(p.getLabel())) {
                    List<ScriptAST.Statement> statements = insertCasesForStatement(p, caze.getStatements());
                    caze.addStatements(statements);
                    res.getCases().add(caze);
                    found = true;
                }
            }
            if(!found) {
                ScriptAST.Case c = new ScriptAST.Case();
                c.setLabel(new CommonToken(ScriptParser.STRING_LITERAL, "\"" + p.getLabel() + "\""));
                res.getCases().add(c);
            }
        }
        return res;
    }

    private static ScriptAST.Statement createCasesForNode(ProofNode pn) {
        return createCasesForNode(pn, new ArrayList<>());
    }
}
