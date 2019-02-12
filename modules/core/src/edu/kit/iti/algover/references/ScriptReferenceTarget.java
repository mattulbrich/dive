package edu.kit.iti.algover.references;

import edu.kit.iti.algover.dafnystructures.DafnyFile;
import edu.kit.iti.algover.proof.ProofNode;
import edu.kit.iti.algover.script.ast.ASTNode;
import org.antlr.runtime.Token;
import org.antlr.v4.runtime.ParserRuleContext;

import java.io.File;

/**
 * ReferenceTarget for scriptnodes as values.
 * <p>
 * One possible use case is a rule application.
 * Not only Terms reference each other between dofferent proofnodes
 * but a rule application is the reason for the
 * term refernces between terms of different proof nodes. Therefore a reference to the
 * correspinding script line shoudl be created as well
 * <p>
 * @author S. Grebing
 */

public class ScriptReferenceTarget<T extends ParserRuleContext> extends ReferenceTarget{


    public File getFile() {
        return file;
    }

    public int getLinenumber() {
        return linenumber;
    }

    public ASTNode getNode() {
        return node;
    }

    private final File file;
    private final int linenumber;
    private final ASTNode node;

    public ScriptReferenceTarget(File file, int linenumber, ASTNode node) {
        this.file = file;
        this.linenumber = linenumber;
        this.node = node;
    }

    @Override
    public <R> R accept(ReferenceTargetVisitor<R> visitor) {
        return visitor.visit(this);
    }

    @Override
    public String toString() {
        return "ScriptReference{" +
                "file=" + file +
                ", linenumber=" + linenumber +
                '}';
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (!(o instanceof ScriptReferenceTarget)) return false;

        ScriptReferenceTarget that = (ScriptReferenceTarget) o;

        if (!file.getName().equals(that.getFile().getName())) return false;
        if (linenumber != that.getLinenumber()) return false;
        return node.equals(that.getNode());
    }

    @Override
    public int hashCode() {
        int result = file.getName().hashCode();
        result = 31 * result + node.hashCode();
        return result;
    }
}


