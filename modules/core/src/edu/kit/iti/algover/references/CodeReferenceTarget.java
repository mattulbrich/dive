/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
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

    //private final DafnyFile file;
    private final Token startToken;
    private final Token endToken;
    private final String filename;

    public CodeReferenceTarget(DafnyFile file, Token startToken, Token endToken) {
        //this.file = file;
        this.filename = file.getFilename();
        this.startToken = startToken;
        this.endToken = endToken;
    }

    public CodeReferenceTarget(String filename, Token startToken, Token endToken) {
        this.filename = filename;
        this.startToken = startToken;
        this.endToken = endToken;
    }

    @Override
    public <R> R accept(ReferenceTargetVisitor<R> visitor) {
        return visitor.visit(this);
    }

  /*  public DafnyFile getFile() {
        return file;
    }*/

    public String getFile(){
        return filename;
    }

    public Token getStartToken() {
        return startToken;
    }

    public Token getEndToken() {
        return endToken;
    }

    @Override
    public String toString() {
        return "CodeReferenceTarget{" +
                "file=" + filename +
                ", startToken=" + startToken +
                ", endToken=" + endToken +
                '}';
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (!(o instanceof CodeReferenceTarget)) return false;

        CodeReferenceTarget that = (CodeReferenceTarget) o;

        //if (!file.getFilename().equals(that.file.getFilename())) return false;
        if (!filename.equals(that.filename)) return false;
        if (startToken.getLine() != that.startToken.getLine()) return false;
        if (startToken.getCharPositionInLine() != that.startToken.getCharPositionInLine()) return false;
        if (endToken.getLine() != that.endToken.getLine()) return false;
        return endToken.getCharPositionInLine() != that.endToken.getCharPositionInLine();
    }

    @Override
    public int hashCode() {
        int result = filename.hashCode();
        result = 31 * result + startToken.hashCode();
        result = 31 * result + endToken.hashCode();
        return result;
    }
}
