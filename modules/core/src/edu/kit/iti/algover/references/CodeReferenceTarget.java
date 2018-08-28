package edu.kit.iti.algover.references;

import edu.kit.iti.algover.dafnystructures.DafnyFile;
import org.antlr.runtime.Token;

/**
 * Encapsulates information about references that point to code.
 * <p>
 * The point referenced can be identified by the DafnyFile and
 * the start and end tokens in the file.
 * <p>
 * Created by Philipp on 27.08.2017.
 */
public class CodeReferenceTarget extends ReferenceTarget {

    private final DafnyFile file;
    private final Token startToken;
    private final Token endToken;

    public CodeReferenceTarget(DafnyFile file, Token startToken, Token endToken) {
        this.file = file;
        this.startToken = startToken;
        this.endToken = endToken;
    }

    @Override
    public <R> R accept(ReferenceTargetVisitor<R> visitor) {
        return visitor.visit(this);
    }

    public DafnyFile getFile() {
        return file;
    }

    public Token getStartToken() {
        return startToken;
    }

    public Token getEndToken() {
        return endToken;
    }

    @Override
    public String toString() {
        return "CodeReference{" +
                "file=" + file +
                ", startToken=" + startToken +
                ", endToken=" + endToken +
                '}';
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (!(o instanceof CodeReferenceTarget)) return false;

        CodeReferenceTarget that = (CodeReferenceTarget) o;

        if (!file.getFilename().equals(that.file.getFilename())) return false;
        if (startToken.getLine() != that.startToken.getLine()) return false;
        if (startToken.getCharPositionInLine() != that.startToken.getCharPositionInLine()) return false;
        if (endToken.getLine() != that.endToken.getLine()) return false;
        return endToken.getCharPositionInLine() != that.endToken.getCharPositionInLine();
    }

    @Override
    public int hashCode() {
        int result = file.getFilename().hashCode();
        result = 31 * result + startToken.hashCode();
        result = 31 * result + endToken.hashCode();
        return result;
    }
}
