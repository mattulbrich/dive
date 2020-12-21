package edu.kit.iti.algover.rule.script;

import edu.kit.iti.algover.PropertyManager;
import edu.kit.iti.algover.nuscript.DefaultScriptASTVisitor;
import edu.kit.iti.algover.nuscript.ScriptAST;
import edu.kit.iti.algover.proof.ProofNode;

import java.util.List;

public class ProofNodeExtractionVisitor extends DefaultScriptASTVisitor<Void, ProofNode, IllegalArgumentException> {

    protected ProofNode getPNforList(ScriptAST.StatementList statementList, ProofNode listRoot) throws IllegalArgumentException {
        List<ScriptAST.Statement> statements = statementList.getStatements();

        if (statements.size() == 0) {
            return listRoot;
        }

        ProofNode ret = statements.get(0).accept(this, null);

        while (ret.getChildren() != null && ret.getChildren().size() == 1) {
            ret = ret.getChildren().get(0);
        }

        if (ret.getChildren() != null && ret.getChildren().size() > 1) {
            // TODO: external second case
            throw new IllegalArgumentException("StatementLists with Cases not eligible for selection yet.");
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
        throw new IllegalArgumentException("StatementLists with Cases not eligible for selection yet.");

    }
}