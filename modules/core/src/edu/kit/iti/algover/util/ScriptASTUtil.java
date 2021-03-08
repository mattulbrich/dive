package edu.kit.iti.algover.util;

import de.uka.ilkd.pp.NoExceptions;
import edu.kit.iti.algover.nuscript.ParentRelationVisitor;
import edu.kit.iti.algover.nuscript.ScriptAST;
import edu.kit.iti.algover.nuscript.ScriptAST.Case;
import edu.kit.iti.algover.nuscript.ScriptAST.Script;
import edu.kit.iti.algover.nuscript.ScriptAST.Statement;
import edu.kit.iti.algover.nuscript.UnsealedCopyVisitor;
import edu.kit.iti.algover.nuscript.parser.ScriptParser;
import edu.kit.iti.algover.proof.Proof;
import edu.kit.iti.algover.proof.ProofNode;
import org.antlr.v4.runtime.CommonToken;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

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
        // pass new Triple<>(newStatement, referenceASTElem, parentAST) a arg
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
     * Remove specified {@link ScriptAST} element from specified {@link Script}.
     * Use specialized {@link UnsealedCopyVisitor} to iterate over script and
     * instantiate new {@link Script} Object
     * @param script
     * @param toBeRemoved
     * @return new {@link Script} that contains all {@link ScriptAST} elements from script except for
     * toBeRemoved.
     */
    public static Script removeStatementFromScript (Script script, ScriptAST toBeRemoved) {
        // Also consider separate class as described in insertAfterStatement
        ScriptAST updated = script.accept(new UnsealedCopyVisitor() {

            protected boolean visitStatements(ScriptAST.StatementList old,
                                           ScriptAST.StatementList newList,
                                           ScriptAST toBeRemoved) {
                if (old == toBeRemoved) {
                    newList.getStatements().clear();
                    return true;
                } else {
                    for (Statement statement : old.getStatements()) {
                        if (statement != toBeRemoved) {
                            newList.addStatement((Statement) statement.accept(this, newList));
                        }
                    }
                }

                return false;

            }

            @Override
            public Script visitScript(Script script, ScriptAST arg) throws NoExceptions {
                Script ret = new Script();
                visitStatements(script, ret, toBeRemoved);
                ret.setParent(arg);

                return ret;
            }

            @Override
            public Case visitCase(Case aCase, ScriptAST arg) throws NoExceptions {
                Case ret = new Case();
                ret.setLabel(aCase.getLabel());

                visitStatements(aCase, ret, toBeRemoved);

                ret.setProofNode(aCase.getProofNode());
                ret.setParent(arg);

                return ret;
            }


        }, null);


        return (Script) updated;
    }

    public static Script insertMissingCases(ProofNode root, Script script) {
        Script scriptCopy = UnsealedCopyVisitor.INSTANCE.visitScript(script, null);

        // not very pretty still
        List<Statement> updatedStatements = insertCasesForStatement(root, script);
        scriptCopy.getStatements().clear();
        scriptCopy.getStatements().addAll(updatedStatements);

        ParentRelationVisitor.setParentRelation(scriptCopy);

        return scriptCopy;
    }


    public static List<ScriptAST.Statement> insertCasesForStatement(ProofNode root, Script script) {
        Script scriptCopy = UnsealedCopyVisitor.INSTANCE.visitScript(script, null);
        List<Statement> stmts = scriptCopy.getStatements();
        return insertCasesForStatement(root, stmts);
    }
    /**
     * recursively inserts all missing case statements in the given script
     *
     * @param root the proofnode for which the cases should be inserted
     * @param stmts the current script that should be extended by the missing case statements
     * @return a new script containing all necessary case statements
     */
    private static List<ScriptAST.Statement> insertCasesForStatement(ProofNode root, List<Statement> stmts) {
        if(stmts.size() == 0) {
            return stmts;
        }
        List<ScriptAST.Statement> result = new ArrayList<>();
        for (int i = 0; i < stmts.size(); ++i) {
            if(stmts.get(i) instanceof ScriptAST.Command) {
                List<ProofNode> pns = getPNsForAST(root, stmts.get(i));
                if (pns.size() == 1) {
                    //no branching rule. nothing to do
                    result.add(stmts.get(i));
                } else if (pns.size() > 1) {
                    result.add(stmts.get(i));
                    //branching rule
                    //next statement has to be a cases
                    if(i + 1 >= stmts.size()) {
                        //there is no next statement so we have to insert the cases
                        result.add(createCasesForNode(pns.get(0).getParent()));
                    } else if(stmts.get(i + 1) instanceof ScriptAST.Cases) {
                        ScriptAST.Cases cases = (ScriptAST.Cases) stmts.get(i + 1);
                        if(cases.getCases().size() == pns.size() || cases.getCases().size() == pns.size() - 1) {
                            //all cases already covered OR one implicit case still open. both leave nothing to do.
                            result.add(cases);
                            ++i;
                        } else {
                            //there are at least 2 cases missing which means something has to be added.
                            ScriptAST.Cases casesCopy =  UnsealedCopyVisitor.INSTANCE.visitCases(cases, null);
                            result.add(createCasesForNode(pns.get(0).getParent(), casesCopy.getCases()));
                        }
                    }
                } else {
                    //TODO error handling
                    return stmts;
                }
            }
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

    public static List<ProofNode> getPNsForAST(Proof proof, ScriptAST astNode) {
        return getPNsForAST(proof.getProofRoot(), astNode);
    }

    public static List<ProofNode> getPNsForAST(ProofNode root, ScriptAST astNode) {
        if(root == null) {
            return new ArrayList<>();
        }
        if(root.getCommand() != null && root.getCommand().equals(astNode)) {
            return Collections.singletonList(root);
        }
        List<ProofNode> res = new ArrayList<>();
        if(root.getChildren() != null) {
            for (ProofNode ch : root.getChildren()) {
                res.addAll(getPNsForAST(ch, astNode));
            }
        }
        return res;
    }

    public static ScriptAST.Command getASTForPN(ProofNode root, ProofNode pn) {
        if(root.equals(pn)) {
            return pn.getCommand();
        }

        if (root.getChildren() == null) {
            return root.getCommand();
        }

        for(ProofNode ch : root.getChildren()) {
            ScriptAST.Command t = getASTForPN(ch, pn);
            if(t != null) {
                return t;
            }
        }
        return null;
    }

    public static ScriptAST getASTListFromPN(ProofNode displayedNode) {
        ScriptAST.StatementList parentList = (ScriptAST.StatementList) displayedNode.getCommand().getParent();
        ScriptAST highlight = parentList;
        for (int i = 0; i < parentList.getStatements().size() - 1; ++i) {
            ScriptAST.Statement stmt = parentList.getStatements().get(i);
            if (stmt == displayedNode.getCommand()) {
                ScriptAST.Statement nextStmt = parentList.getStatements().get(i + 1);
                // Use visitor?
                if (nextStmt instanceof ScriptAST.Cases) {
                    ScriptAST.Cases cases = (ScriptAST.Cases) nextStmt;
                    for (int j = 0; j < displayedNode.getParent().getChildren().size(); j++) {
                        // TODO: tests and assertions
                        // Handle implicit cases
                        ProofNode pChild = displayedNode.getParent().getChildren().get(j);
                        if (pChild == displayedNode) {
                            if (j < cases.getCases().size()) {
                                return cases.getCases().get(j);
                            }
                        }
                    }
                } else {
                    return displayedNode.getCommand().getParent();
                }
            }
        }
        return highlight;
    }

}
