/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.term.prettyprint;

import de.uka.ilkd.pp.Backend;
import de.uka.ilkd.pp.NoExceptions;
import edu.kit.iti.algover.util.Pair;
import nonnull.NonNull;

import javax.swing.text.AttributeSet;
import javax.swing.text.BadLocationException;
import javax.swing.text.Document;
import java.util.*;

import edu.kit.iti.algover.rules.SubtermSelector;

/**
 * This class is used to render pretty-printed strings. It is used as a
 * {@link Backend} for the jpp library.
 *
 * This class allows building a string of nested blocks, each annotated with a
 * {@link SubtermSelector}. The last matching block points to the topmost term
 * to which a character belongs.
 *
 * Additionally styles may be set for sections of the text which will be used to
 * render terms on the screen.
 */
public class AnnotatedString implements Backend<NoExceptions> {

    /**
     * Interface which is used to convert styles to attributes. Implemented by
     * the GUI.
     */
    public interface AttributeSetFactory {

        /**
         * given a set of styles return a swing attribute set
         * that represents this list.
         *
         * @param styles the styles
         * @return an attribute set which matches the style description
         */
        public AttributeSet makeStyle(Set<Style> styles);
    }

    /**
     * The styles which can be applied to sections of the text.
     */
    public enum Style {
        /**
         * for annotated types ("as type").
         */
        TYPE,
        /**
         * for object variables.
         */
        VARIABLE,
        /**
         * for update modalities.
         */
        UPDATE,
        /**
         * fhe program modalities.
         */
        PROGRAM,
        /**
         * for individual statements.
         */
        STATEMENT,
        /**
         * for highlighting keywords of the programming language.
         */
        KEYWORD,
        /**
         * The node is an inner node and this should be reflected in the terms.
         */
        CLOSED,
        /**
         * Program variables have diferent colors again.
         */
        ASSIGNABLE
    }

    /**
     * The Class Element is used to keep information on one annotated block.
     */
    public static class TermElement {

        /**
         * The begining of the block.
         */
        private int begin;

        /**
         * The end of the block.
         */
        private int end;

        /**
         * The subterm selector of the term to which this element points.
         */
        private SubtermSelector attr;

        /**
         * Instantiates a new term element.
         */
        private TermElement() {
            // hide constructor from outside
        }

        /* (non-Javadoc)
         * @see java.lang.Object#toString()
         * used in testing
         */
        @Override public String toString() {
            return "Element[begin=" + begin + ";end=" + end + ";attr=" + attr
                    + "]";
        }

        /**
         * Gets the beginning of the term element.
         *
         * @return the index into the string marking the beginning.
         */
        public int getBegin() {
            return begin;
        }

        /**
         * Gets the end of the term element.
         *
         * @return the index into the string marking the end.
         */
        public int getEnd() {
            return end;
        }

        /**
         * Gets the subterm selector of the section.
         *
         * @return the subterm selector to which the element points.
         */
        public SubtermSelector getSubtermSelector() {
            return attr;
        }

    }

    /**
     * We push newly created annotations on this stack.
     */
    private final Stack<TermElement> elementStack = new Stack<TermElement>();

    /**
     * The list of all annotated elements.
     */
    private final List<TermElement> allElements = new ArrayList<TermElement>();

    /**
     * The style stack keeps a history of style annotations
     */
    private final Stack<Style> styleStack = new Stack<Style>();

    /**
     * The width of a single line.
     */
    private final int linewidth;

    /**
     * The styled output holds formatted sections with their styles and contents.
     */
    private final List<Pair<Set<Style>, String>> styledOutput =
            new ArrayList<Pair<Set<Style>, String>>();

    /**
     * The underlying builder that is used to construct the result.
     */
    private final StringBuilder curBuilder = new StringBuilder();

    /**
     * The number of characters written so far.
     */
    private int writtenChars = 0;

    /**
     * Instantiates a new annotated string.
     *
     * @param linewidth
     *            number of character per line, a number greater than zero.
     */
    public AnnotatedString(int linewidth) {
        this.linewidth = linewidth;
    }

    /* (non-Javadoc)
     * @see de.uka.ilkd.pp.Backend#print(java.lang.String)
     */
    @Override
    public void print(String s) {
        curBuilder.append(s);
        writtenChars += s.length();
    }

    /* (non-Javadoc)
     * @see de.uka.ilkd.pp.Backend#newLine()
     */
    @Override
    public void newLine(){
        print("\n");
    }

    /* (non-Javadoc)
     * @see de.uka.ilkd.pp.Backend#close()
     */
    @Override
    public void close() {
        // nothing to be done
    }

    /* (non-Javadoc)
     * @see de.uka.ilkd.pp.Backend#flush()
     */
    @Override
    public void flush() {
        // nothing to be done
    }

    /* (non-Javadoc)
     * @see de.uka.ilkd.pp.Backend#mark(java.lang.Object)
     */
    @Override
    public void mark(Object o) {
        assert o instanceof LayoutMark : "only layoutmarks supported!";
        ((LayoutMark)o).handle(this);
    }

    /* (non-Javadoc)
     * @see de.uka.ilkd.pp.Backend#lineWidth()
     */
    @Override
    public int lineWidth() {
        return linewidth;
    }

    /* (non-Javadoc)
     * @see de.uka.ilkd.pp.Backend#measure(java.lang.String)
     */
    @Override
    public int measure(String s) {
        return s.length();
    }

    /**
     * The number of characters that have been written to the stream so far.
     *
     * @return a non-negative integer
     */
    public int length() {
        return writtenChars;
    }

    /**
     * Gets a lists of all term elements in this string. This does not include
     * the toplevel term element which is implicit.
     *
     * @return an immutable list
     */
    public List<TermElement> getAllTermElements() {
        return Collections.unmodifiableList(allElements);
    }

    /**
     * Gets the term element at an index in the string.
     *
     * If no subterm is responsible for the posiiton, it is attributed to the
     * toplevel.
     *
     * @param index
     *            the index into the string
     * @return the term element for this point.
     */
    public @NonNull TermElement getTermElementAt(int index) {
        TermElement retval = null;
        for (TermElement element : allElements) {
            if (element.begin <= index && element.end > index) {
                retval = element;
            }

            if (element.begin > index) {
                break;
            }
        }
        if(retval == null) {
            retval = new TermElement();
            retval.end = length();
            retval.attr = new SubtermSelector();
        }
        return retval;
    }

    /**
     * Append to document.
     *
     * @param document the document
     * @param attributeFactory the attribute factory
     */
    public void appendToDocument(Document document, AttributeSetFactory attributeFactory) {
        try {
            for (Pair<Set<Style>, String> pair : styledOutput) {
                AttributeSet attr = attributeFactory.makeStyle(pair.fst);
                document.insertString(document.getLength(), pair.snd, attr);
            }
            if(curBuilder.length() > 0) {
                Set<Style> set = EnumSet.noneOf(Style.class);
                set.addAll(styleStack);
                AttributeSet attr = attributeFactory.makeStyle(set);
                document.insertString(document.getLength(), curBuilder.toString(), attr);
            }
        } catch (BadLocationException e) {
            // designed not top happen
            throw new Error(e);
        }
    }

    /**
     * Checks if all stacks have been emptied.
     *
     * Good for ensuring that the pretty-printing did not fail.
     * Can be used in assertions.
     *
     * @return true, if all stacks are empty
     */
    public boolean hasEmptyStacks() {
        return styleStack.isEmpty() && elementStack.isEmpty();
    }

    /**
     * Handle a "begin term" marker.
     *
     * @param subtermno
     *            the number of the sub term (index into the parents' children)
     */
    public void handleBeginTerm(int subtermno) {
        TermElement el = new TermElement();
        el.begin = length();
        if(elementStack.isEmpty()) {
            el.attr = new SubtermSelector(subtermno);
        } else {
            TermElement top = elementStack.peek();
            el.attr = new SubtermSelector(top.attr, subtermno);
        }
        elementStack.push(el);
        allElements.add(el);
    }

    /**
     * Handle a "end term" marker.
     */
    public void handleEndTerm() {
        TermElement top = elementStack.pop();
        top.end = length();
    }

    /**
     * Handle a "push style" marker.
     *
     * Push the style onto the stack and flush the section.
     *
     * @param style the style to add
     */
    public void handlePushStyle(Style style) {
        finishStyles();
        styleStack.push(style);
    }

    /**
     * Handle a "pop style" marker.
     *
     * Pop the style fromthe stack and flush the section.
     */
    public void handlePopStyle() {
        finishStyles();
        styleStack.pop();
    }

    /*
     * Flush the styles to styledOutput
     */
    private void finishStyles() {
        if(curBuilder.length() > 0) {
            Set<Style> set = EnumSet.noneOf(Style.class);
            set.addAll(styleStack);
            styledOutput.add(new Pair<>(set, curBuilder.toString()));
            curBuilder.setLength(0);
        }
    }

    /* (non-Javadoc)
     * @see java.lang.Object#toString()
     */
    @Override
    public String toString() {
        StringBuilder res = new StringBuilder();
        for (Pair<Set<Style>, String> pair : styledOutput) {
            res.append(pair.getSnd());
        }
        res.append(curBuilder);
        return res.toString();
    }

    /**
     * Describe the array of all term elements in a string. Used in test cases
     *
     * @return a string describing the set of all elements.
     */
    String describeAllElements() {
        return allElements.toString();
    }

    /**
     * Describe the array of all styled sections in a string. Used in test cases
     *
     * @return a string describing the styled output
     */
    String describeStyledOutput() {
        return styledOutput.toString();
    }

}
