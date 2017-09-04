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
public class CodeReference extends Reference {

    private final DafnyFile file;
    private final Token startToken;
    private final Token endToken;

    public CodeReference(DafnyFile file, Token startToken, Token endToken) {
        this.file = file;
        this.startToken = startToken;
        this.endToken = endToken;
    }

    @Override
    public <R> R accept(ReferenceVisitor<R> visitor) {
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
}
