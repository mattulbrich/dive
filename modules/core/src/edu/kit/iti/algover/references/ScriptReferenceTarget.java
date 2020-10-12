package edu.kit.iti.algover.references;

import edu.kit.iti.algover.nuscript.ScriptAST;
import edu.kit.iti.algover.proof.PVC;

/**
 * ReferenceTarget for scriptnodes as values.
 * <p>
 * One possible use case is a rule application.
 * Not only Terms reference each other between different proofnodes
 * but a rule application is the reason for the
 * term references between terms of different proof nodes. Therefore a reference to the
 * corresponding script line should be created as well
 * <p>
 * @author S. Grebing
 */

public class ScriptReferenceTarget extends ReferenceTarget {

    private final PVC pvc;
    private final ScriptAST node;

    public ScriptReferenceTarget(PVC pvc, ScriptAST node) {
        this.pvc = pvc;
        this.node = node;
    }

    @Override
    public <R> R accept(ReferenceTargetVisitor<R> visitor) {
        return visitor.visit(this);
    }

    @Override
    public String toString() {
        return "ScriptReferenceTarget{" +
                "pvc=" + pvc +
                ", ast=" + node +
                '}';
    }

    public int getLinenumber() {
        return node.getBeginToken().getLine();
    }

    public PVC getPvc() {
        return pvc;
    }

    public ScriptAST getNode() {
        return node;
    }

}


