/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */


/*
 * This file is part of
 *    ivil - Interactive Verification on Intermediate Language
 *
 * Copyright (C) 2009-2012 Karlsruhe Institute of Technology
 *
 * The system is protected by the GNU General Public License.
 * See LICENSE.TXT (distributed with this file) for details.
 */

package edu.kit.iti.algover.term.prettyprint;

import edu.kit.iti.algover.term.prettyprint.AnnotatedString.Style;
import edu.kit.iti.algover.term.Term;
import nonnull.Nullable;

import java.beans.PropertyChangeListener;
import java.beans.PropertyChangeSupport;
import java.util.Objects;

/**
 * This class is the entry point to the pretty priting system. There are
 * static and dynamic entry points to this class.
 *
 * <pre>
 * PrettyPrint.print(env, term)
 * </pre>
 *
 * can be used to write a term sporadically.
 *
 * An {@link AnnotatedString} is returned by the methods, possibly with
 * linebreaks.
 *
 * This class is taken from ivil.
 *
 * @see AnnotatedString
 * @author mulbrich
 */
public class PrettyPrint {

    public static final String TYPED_PROPERTY = "pseudo.pp.typed";
    public static final String PRINT_FIX_PROPERTY = "pseudo.pp.printFix";
    public static final String PRINT_PLUGINS_PROPERTY = "pseudo.pp.printPlugins";
    public static final String INITIALSTYLE_PROPERTY = "pseudo.pp.initialstyle";
    public static final String BREAK_MODALITIES_PROPERTY = "pseudo.pp.breakModalities";
    public static final String SERVICE_NAME = "prettyPrinter";

    /**
     * whether or not in-/prefix operators are printed as such.
     */
    private boolean printFix = true;

    /**
     * the style (attribute string) to be set in the beginning.
     * may be null if no special attributes are to be set.
     */
    private Style initialStyle;

    /**
     * create a new pretty printer with the default properties preset.
     */
    public PrettyPrint() {
    }

    /**
     * pretty print a term using the currently set properties on this object.
     *
     * The result is an annotated String in which to every character the
     * innermost containing subterm can be obtained.
     *
     * @param term
     *            the term to pretty print
     * @return a freshly created annotated string object
     */
    public AnnotatedString print(Term term) {
        return print(term, Integer.MAX_VALUE);
    }

    /**
     * pretty print a term using the currently set properties on this object.
     *
     * The result is an annotated String in which to every character the
     * innermost containing subterm can be obtained.
     *
     * @param term
     *            the term to pretty print
     *
     * @param linewidth
     *            length of a line, a positive number
     *
     * @return a freshly created annotated string object
     */
    public AnnotatedString print(Term term, int linewidth) {
        return print(term, new PrettyPrintLayouter(linewidth));
    }

    /**
     * pretty print a term using the currently set properties on this object.
     *
     * The result is an annotated String in which to every character the
     * innermost containing subterm can be obtained.
     *
     * @param term
     *            the term to pretty print
     * @param printer
     *            the annotated string to append the term to
     * @return printer
     */
    private AnnotatedString print(Term term, PrettyPrintLayouter printer) {
        PrettyPrintVisitor visitor = new PrettyPrintVisitor(this, printer);

        if(initialStyle != null) {
            printer.setStyle(initialStyle);
        }

        term.accept(visitor, null);

        if(initialStyle != null) {
            printer.resetPreviousStyle();
        }

        assert printer.hasEmptyStack() :
            "Cannot render: " + term;

        return printer.getAnnotatedString();
    }

    /**
     * Checks if the printer is printing infix and prefix.
     *
     * @return true, if is printing fix
     */
    public boolean isPrintingFix() {
        return printFix;
    }

    /**
     * Sets the printing fix.
     *
     * All registered {@link PropertyChangeListener} are informed of this
     * change if the current value differs from the set value.
     *
     * @param printFix the new printing fix
     */
    public void setPrintingFix(boolean printFix) {
        boolean old = this.printFix;
        this.printFix = printFix;
        firePropertyChanged(PRINT_FIX_PROPERTY, old, printFix);
    }

    /**
     * The system to manage properties
     */
    private PropertyChangeSupport propertiesSupport;

    /**
     * get the style (attribute string) that is to be set in the beginning
     *
     * @return a string or possibly null
     */
    public @Nullable Style getInitialStyle() {
        return initialStyle;
    }

    /**
     * set the style (attribute string) that is to be set in the beginning.
     *
     * All registered {@link PropertyChangeListener} are informed of this
     * change if the current value differs from the set value.
     *
     * @param initialStyle
     *   the style to be set at top level, or null if none is to be set
     */
    public void setInitialStyle(@Nullable Style initialStyle) {
        Style old = this.initialStyle;
        this.initialStyle = initialStyle;
        firePropertyChanged(INITIALSTYLE_PROPERTY, old, initialStyle);
    }

    /**
     * Adds the property change listener.
     *
     * @param listener
     *            the listener
     */
    public void addPropertyChangeListener(PropertyChangeListener listener) {
        if(propertiesSupport == null) {
            propertiesSupport = new PropertyChangeSupport(this);
        }
        propertiesSupport.addPropertyChangeListener(listener);
    }

    /**
     * Adds a property change listener for a particular property.
     *
     * @param property
     *            the property
     * @param listener
     *            the listener
     */
    public void addPropertyChangeListener(String property,
            PropertyChangeListener listener) {
        if(propertiesSupport == null) {
            propertiesSupport = new PropertyChangeSupport(this);
        }
        propertiesSupport.addPropertyChangeListener(property, listener);
    }

    /**
     * Removes the property change listener.
     *
     * @param listener the listener
     */
    public void removePropertyChangeListener(PropertyChangeListener listener) {
        if(propertiesSupport != null) {
            propertiesSupport.removePropertyChangeListener(listener);
        }
    }

    /**
     * Fire property changed.
     *
     * @param property
     *            the property
     * @param oldVal
     *            the old value
     * @param newVal
     *            the new value
     */
    private <E> void firePropertyChanged(String property, E oldVal, E newVal) {
        if(propertiesSupport != null && !Objects.equals(oldVal, newVal)) {
            propertiesSupport.firePropertyChange(property, oldVal, newVal);
        }
    }

}
