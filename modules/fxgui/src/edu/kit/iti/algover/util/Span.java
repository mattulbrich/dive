package edu.kit.iti.algover.util;

/**
 * Created by Philipp on 22.07.2017.
 */
public class Span {
    public final int beginLine, endLine, beginCharInLine, endCharInLine;

    public Span(int beginLine, int endLine, int beginCharInLine, int endCharInLine) {
        this.beginLine = beginLine;
        this.endLine = endLine;
        this.beginCharInLine = beginCharInLine;
        this.endCharInLine = endCharInLine;
    }

    public boolean isInvalid() {
        return beginCharInLine == -1;
    }

    public static Span union(Span one, Span other) {
        if (one.isInvalid()) return other;
        if (other.isInvalid()) return one;
        return new Span(
                Math.min(one.beginLine, other.beginLine),
                Math.max(one.endLine, other.endLine),
                Math.min(one.beginCharInLine, other.beginCharInLine),
                Math.max(one.endCharInLine, other.endCharInLine)
        );
    }

    public boolean containsPosition(int line, int charInLine) {
        return
                beginLine <= line && line <= endLine
                        && (line != beginLine || beginCharInLine <= charInLine)
                        && (line != endLine || charInLine <= endCharInLine);
    }

    public String toString() {
        return "Span(" + beginLine + ":" + beginCharInLine + " to " + endLine + ":" + endCharInLine + ")";
    }
}
