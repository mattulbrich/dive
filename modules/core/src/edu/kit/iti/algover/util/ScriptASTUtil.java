package edu.kit.iti.algover.util;

import de.uka.ilkd.pp.NoExceptions;
import edu.kit.iti.algover.nuscript.*;
import edu.kit.iti.algover.nuscript.ScriptAST.Script;
import edu.kit.iti.algover.nuscript.ScriptAST.Statement;
import edu.kit.iti.algover.nuscript.ScriptAST.Case;
import edu.kit.iti.algover.nuscript.parser.ScriptParser;
import edu.kit.iti.algover.proof.ProofNode;

import org.antlr.v4.runtime.CommonToken;

import java.util.ArrayList;
import java.util.List;
import java.util.logging.Logger;

/**
 * Utility class for Creating new ScriptASTs. Used for inserting a new Statement
 * into a given ScriptAST.Script
 *
 * @author Valentin Springsklee
 *
 */
public class ScriptASTUtil {

    private ScriptASTUtil() {
        throw new Error();
    }

    public static Script insertStatementAfter(Script script, Statement newStatement, ScriptAST referenceASTElem) {
        // Maybe implement InsertAfterStatementVisitor class, extends
        // DefaultScriptASTVisitor<Triple<Statement, ScriptAST, ScriptAST>, ScriptAST, SomeException>
        // pass new Triple<>(newStatement, referenceStatememnt, parentAST) a arg
        ScriptAST updated = script.accept(new UnsealedCopyVisitor() {

            protected void visitStatements(ScriptAST.StatementList old,
                                           ScriptAST.StatementList newList,
                                           Statement newStatement,
                                           ScriptAST referenceASTElem) {
                for (Statement statement : old.getStatements()) {
                    if (statement == referenceASTElem) {
                        newList.addStatement(newStatement);
                        newStatement.setParent(newList);
                    }
                    newList.addStatement((Statement) statement.accept(this, newList));
                }

                if (old == referenceASTElem) {
                    newList.addStatement(newStatement);
                    newStatement.setParent(newList);
                }
            }

            @Override
            public Script visitScript(Script script, ScriptAST arg) throws NoExceptions {
                Script ret = new Script();
                visitStatements(script, ret, newStatement, referenceASTElem);
                ret.setParent(arg);

                return ret;
            }

            @Override
            public Case visitCase(Case aCase, ScriptAST arg) throws NoExceptions {
                Case ret = new Case();
                ret.setLabel(aCase.getLabel());

                visitStatements(aCase, ret, newStatement, referenceASTElem);

                ret.setProofNode(aCase.getProofNode());
                ret.setParent(arg);

                return ret;
            }


        }, null);


        return (Script) updated;
    }

    /**
     * recursively inserts all missing case statements in the given script
     *
     * @param pn the proofnode for which the cases should be inserted
     * @param stmts the current script that should be extended by the missing case statements
     * @return a new script containing all necessary case statements
     */
    // MU: Adapted the existing code to nuscript. But it does not seem to be recursive at all.
    // TODO: Make it work for "implicit" second cases (syntax level)
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
                // apparently some guards are string literals and some are MathcExpressions...
                String caseString = Util.stripQuotes(caze.getLabel().getText());
                if (caseString.equals(p.getLabel())) {
                    List<ScriptAST.Statement> statements = insertCasesForStatement(p, caze.getStatements());
                    caze.setStatements(statements);
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
