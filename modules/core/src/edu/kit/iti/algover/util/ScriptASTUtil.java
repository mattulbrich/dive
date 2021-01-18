package edu.kit.iti.algover.util;

import edu.kit.iti.algover.nuscript.DefaultScriptASTVisitor;
import edu.kit.iti.algover.nuscript.ParentRelationVisitor;
import edu.kit.iti.algover.nuscript.ScriptAST;
import edu.kit.iti.algover.nuscript.ScriptAST.Script;
import edu.kit.iti.algover.nuscript.ScriptAST.Statement;
import edu.kit.iti.algover.nuscript.ScriptAST.Cases;
import edu.kit.iti.algover.nuscript.ScriptAST.Case;
import edu.kit.iti.algover.nuscript.ScriptAST.Command;
import edu.kit.iti.algover.nuscript.parser.ScriptParser;
import edu.kit.iti.algover.proof.ProofNode;

import org.antlr.v4.runtime.CommonToken;

import java.util.ArrayList;
import java.util.List;
import java.util.logging.Logger;

/**
 * Utility class for Creating new ScriptASTs. Used for inserting a new Statement
 * into a given ScriptAST.Script
 * Could and probabily will be extended to insert any statement after a given statement.
 *
 * @author Valentin Springsklee
 *
 */
public class ScriptASTUtil {

    private ScriptASTUtil() {
        throw new Error();
    }

    public static Script createScriptWithStatements(List<Statement> statements) {
        Script script = new Script();
        script.getStatements().addAll(statements);
        ParentRelationVisitor.setParentRelation(script);
        return script;
    }


    public static Case createEmptyCaseFrom(Case oldCase) {
        Case newCase = new Case();
        newCase.setLabel(oldCase.getLabel());
        newCase.setProofNode(oldCase.getProofNode());

        return newCase;
    }


    public static Script insertIntoCase(Script script, Statement newStatement, Case target) {
        Script updatedScript = new Script();

        for (Statement stmt: script.getStatements()) {
            updatedScript.addStatement(stmt.accept(new DefaultScriptASTVisitor<Void, Statement, RuntimeException>() {
                @Override
                public Command visitCommand(Command command, Void arg) throws RuntimeException {
                    return command;
                }

                @Override
                public Cases visitCases(Cases cases, Void arg) throws RuntimeException {
                    Cases newCases = new Cases();
                    for (Case c: cases.getCases()) {
                        Case newCase = createEmptyCaseFrom(c);
                        for (Statement stmtC: c.getStatements()) {
                            newCase.addStatement(stmtC.accept(this, null));
                        }
                        if (c == target) {
                            newCase.addStatement(newStatement);
                        }
                        newCases.addCase(newCase);
                    }
                    return newCases;
                }
            }, null));
        }

        ParentRelationVisitor.setParentRelation(updatedScript);

        return updatedScript;
    }

    /**
     * recursively inserts all missing case statements in the given script
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
        if((pn.getChildren() == null || pn.getSuccessors().size() == 1) && st instanceof ScriptAST.Command) {
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
     * @return a case statement containing all necessary cases
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

    public static List<Statement> insertStatementAfter(List<Statement>  statements, Statement newStatement, ScriptAST referenceStatement) {
        for(int i = 0; i < statements.size(); ++i) {
            if(statements.get(i) == referenceStatement) {
                statements.add(i + 1, newStatement);
                return statements;
            }
            if(statements.get(i) instanceof Cases) {
                for(int j = 0; j < ((Cases) statements.get(i)).getCases().size(); ++j) {
                    List<Statement> res = insertStatementAfter(((Cases) statements.get(i)).getCases().get(j).getStatements(), newStatement, referenceStatement);
                    if(res != null) {
                        return res;
                    }
                }
            }
        }
        return null;
    }

    public static Script insertStatementAfter(Script script, Statement newStatement, Statement referenceStatement) {
        List<Statement> res = insertStatementAfter(script.getStatements(), newStatement, referenceStatement);
        if(res == null) {
            System.out.println("Couldnt find reference statement to insert new statement.");
        }
        return script;

    }
}
