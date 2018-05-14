/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.term.prettyprint;

import de.uka.ilkd.pp.Layouter;
import de.uka.ilkd.pp.NoExceptions;
import edu.kit.iti.algover.term.prettyprint.AnnotatedString.Style;
import nonnull.NonNull;

/**
 * The Class PrettyPrintLayouter is an internal class of the prettyprinting
 * system. It is the interface to the jpplib.
 */
class PrettyPrintLayouter {

    /**
     * The default value for indentation.
     */
    public static final int DEFAULT_INDENTATION = 4;

    /**
     * The backend is an {@link AnnotatedString} to which everything is dumped
     */
    private final AnnotatedString backend;

    /**
     * The layouter is the frontend of the jpp.
     */
    private final Layouter<NoExceptions> layouter;

    /**
     * The last character written. Needed for checking of double operators "! !"
     */
    private char lastCharacter;

    /**
     * a counter for keeping track of changes
     */
    private int modCount;

    /**
     * Instantiates a new pretty print layouter without length limit.
     */
    public PrettyPrintLayouter() {
        this(Integer.MAX_VALUE);
    }

    /**
     * Instantiates a new pretty print layouter for a fixed line length.
     *
     * @param linewidth the number of characters in a line, {@code >= 1}
     */
    public PrettyPrintLayouter(int linewidth) {
        backend = new AnnotatedString(linewidth);
        layouter = new Layouter<NoExceptions>(backend, DEFAULT_INDENTATION);
    }

    /**
     * Sets a new style for the next characters. The style is added to the other
     * already present
     *
     * @param style
     *            the style to add
     *
     * @return a reference to <tt>this</tt>
     */
    public PrettyPrintLayouter setStyle(@NonNull Style style) {
        layouter.mark(new LayoutMark.PushStyle(style));
        return this;
    }

    /**
     * Appends an arbitrary text.
     *
     * @param string to write
     * @return a reference to <tt>this</tt>
     */
    public PrettyPrintLayouter append(@NonNull String string) {
        layouter.print(string);
        if(!string.isEmpty()) {
            // MU: added this if-condition as bugfix
            lastCharacter = string.charAt(string.length() - 1);
        }
        modCount ++;
        return this;
    }

    /**
     * Remove the previously added style.
     *
     * @return  a reference to <tt>this</tt>
     */
    public PrettyPrintLayouter resetPreviousStyle() {
        layouter.mark(new LayoutMark.PopStyle());
        return this;
    }

    /**
     * Get the number of changes made so far.
     *
     * This can be used to determine if anything has been written to the
     * layouter in the meantime.
     *
     * @return a number which increases on every change.
     */
    public int getModificationCounter() {
        return modCount;
    }

    /**
     * send an according
     *
     * @return  a reference to <tt>this</tt>
     */
    public PrettyPrintLayouter endTerm() {
        layouter.mark(new LayoutMark.EndTerm());
        return this;
    }

    /**
     * Begin term.
     *
     * @param currentSubTermIndex the current sub term index
     * @return  a reference to <tt>this</tt>
     */
    public PrettyPrintLayouter beginTerm(int... currentSubTermIndex) {
        layouter.mark(new LayoutMark.BeginTerm(currentSubTermIndex));
        return this;
    }

    /**
     * Checks if all stacks have been emptied.
     *
     * Good for ensuring that all pretty-printing blocks were closed.
     * Can be used in assertions.
     *
     * @return true, if all stacks are empty
     */
    public boolean hasEmptyStack() {
        return backend.hasEmptyStacks();
    }

    /**
     * Gets the last character of the stream.
     *
     * Returns 0 if the stream is empty.
     *
     * @return the last character
     */
    public char getLastCharacter() {
        return lastCharacter;
    }

    /**
     * Gets the underlying annotated string.
     *
     * @return the annotated string
     */
    public @NonNull
    AnnotatedString getAnnotatedString() {
        return backend;
    }

    /**
     * Begin a new block.
     *
     * Add <code>indent</code> to the indentation level, relative to the current
     * position.
     *
     * @param indent
     *            the indentation for this block
     * @return
     *
     */
    public PrettyPrintLayouter beginBlock(int indent) {
        layouter.beginC(indent);
        return this;
    }

    /**
     * Ends the innermost block.
     * @return
     *
     * @return a reference to <tt>this</tt>
     */
    public PrettyPrintLayouter endBlock() {
        layouter.end();
        return this;
    }

    /**
     *
     * Indent relative to the indentation level if surrounding block is broken. If
     * the surrounding block fits on one line, insert <code>width</code>
     * spaces. Otherwise, indent to the current indentation level, plus
     * <code>offset</code>, unless that position has already been exceeded on
     * the current line. If that is the case, nothing is printed. No line break
     * is possible at this point.
     *
     * @param spaces
     *            space to insert if not broken
     * @param brokenSpaces
     *            offset relative to current indentation level
     * @return a reference to <tt>this</tt>
     */
    public PrettyPrintLayouter indentBlock(int spaces, int brokenSpaces) {
        if(spaces > 0 && brokenSpaces > 0) {
            // a space will be certainly inserted
            lastCharacter = ' ';
        }
        layouter.ind(spaces, brokenSpaces);
        modCount ++;
        return this;
    }

    /**
     * Print a break. This will print <code>width</code> spaces if the line is
     * <em>not</em> broken at this point. If it <em>is</em> broken,
     * indentation is added to the current indentation level, plus the value of
     * <code>offset</code>.
     *
     * @param spaces
     *            space to insert if not broken
     * @param brokenSpaces
     *            offset relative to current indentation level
     * @return this
     *
     * @return  a reference to <tt>this</tt>
     */
    public PrettyPrintLayouter breakBlock(int spaces, int brokenSpaces) {
        if(spaces > 0) {
            // a space will be certainly inserted
            lastCharacter = ' ';
        }
        layouter.brk(spaces, brokenSpaces);
        modCount ++;
        return this;
    }

}
