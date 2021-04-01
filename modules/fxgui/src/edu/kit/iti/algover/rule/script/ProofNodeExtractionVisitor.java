package edu.kit.iti.algover.rule.script;

import edu.kit.iti.algover.PropertyManager;
import edu.kit.iti.algover.nuscript.DefaultScriptASTVisitor;
import edu.kit.iti.algover.nuscript.ScriptAST;
import edu.kit.iti.algover.proof.ProofNode;

import java.util.List;

/**
 * Visitor to get ProofNode from AST Element.
 *
 * review: consider to implement as singleton.
 *
 * @author Valentin
 */
public class ProofNodeExtractionVisitor extends DefaultScriptASTVisitor<Void, ProofNode, IllegalArgumentException> {

    public static final ProofNodeExtractionVisitor INSTANCE = new ProofNodeExtractionVisitor();

    /**
     * TODO: add documentation
     * @param statementList
     * @param listRoot
     * @return
     * @throws IllegalArgumentException
     */
    protected ProofNode getPNforList(ScriptAST.StatementList statementList, ProofNode listRoot) throws IllegalArgumentException {
        List<ScriptAST.Statement> statements = statementList.getStatements();

        if (statements.size() == 0) {
            return listRoot;
        }

        ProofNode ret = statements.get(0).accept(this, null);

        if (ret == null) {
            return null;
        }

        while (ret.getChildren() != null && ret.getChildren().size() > 0) {
            ret = ret.getChildren().get(ret.getChildren().size() - 1);
        }

        return ret;
    }

    @Override
    public ProofNode visitScript(ScriptAST.Script script, Void arg) throws IllegalArgumentException {
        ProofNode ret = getPNforList(script, PropertyManager.getInstance().currentProof.get().getProofRoot());
        return ret;
    }

    @Override
    public ProofNode visitCase(ScriptAST.Case aCase, Void arg) throws IllegalArgumentException {
        ProofNode ret = getPNforList(aCase, aCase.getProofNode());
        return ret;
    }

    @Override
    public ProofNode visitCommand(ScriptAST.Command command, Void arg) throws IllegalArgumentException {
        return command.getProofNode();
    }

    @Override
    public ProofNode visitCases(ScriptAST.Cases cases, Void arg) throws IllegalArgumentException {
        // TODO: external second case validation and support
        ProofNode ret = null;

        if (cases.getCases().size() > 0) {
            ret = cases.getCases().get(0).getProofNode();
        } else {
            ret = PropertyManager.getInstance().currentProofNode.get();
        }

        return ret;
    }
}