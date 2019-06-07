package edu.kit.iti.algover.references;

import edu.kit.iti.algover.proof.PVC;
import edu.kit.iti.algover.script.ast.ASTNode;

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

public class ScriptReferenceTarget extends ReferenceTarget{


    public PVC getPvc() {
        return pvc;
    }

    public int getLinenumber() {
        return linenumber;
    }

    public ASTNode getNode() {
        return node;
    }

    private PVC pvc;
    private final int linenumber;
    private final ASTNode node;

    public ScriptReferenceTarget(PVC pvc, int linenumber, ASTNode node) {
        this.pvc = pvc;
        this.linenumber = linenumber;
        this.node = node;
    }
    public ScriptReferenceTarget( int linenumber, ASTNode node) {

        this.linenumber = linenumber;
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
                ", linenumber=" + linenumber +
                '}';
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (!(o instanceof ScriptReferenceTarget)) return false;

        ScriptReferenceTarget that = (ScriptReferenceTarget) o;
        if(pvc != null) {
            if (!pvc.getIdentifier().equals(that.getPvc().getIdentifier())) return false;
        }
        if (linenumber != that.getLinenumber()) return false;
        return node.equals(that.getNode());
    }

    @Override
    public int hashCode() {
        int result = 1;
        if(pvc != null) {
            result = pvc.getIdentifier().hashCode();
        }
        result = 31 * result + node.hashCode();
        return result;
    }
}


