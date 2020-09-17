/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
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

import edu.kit.iti.algover.proof.ProofFormula;
import edu.kit.iti.algover.term.FunctionSymbol;
import edu.kit.iti.algover.term.Sequent;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.term.VariableTerm;
import edu.kit.iti.algover.term.prettyprint.AnnotatedString.Style;
import edu.kit.iti.algover.util.Util;
import nonnull.NonNull;
import nonnull.Nullable;

import java.beans.PropertyChangeListener;
import java.beans.PropertyChangeSupport;
import java.util.*;

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
     * This constant collects all installed {@link PrettyPrintExtension}s.
     */
    private static final List<PrettyPrintExtension> EXTENSIONS =
            Collections.unmodifiableList(
                    Util.toList(ServiceLoader.load(PrettyPrintExtension.class)));

    /**
     * The map which caches the extensions responsible for printing certain
     * function symbols. With this mapping, it need not be checked which function
     * symbol is to be used for a function symbol.
     */
    private final
    @NonNull
    Map<FunctionSymbol, PrettyPrintExtension> responsibleExtensions =
            new HashMap<>();

    private final VariablePrettyPrintExtension variablePrettyPrintExtension = new SubscriptPrinterExtension();
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
     * The system to manage properties
     */
    private PropertyChangeSupport propertiesSupport;

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
     * @param term      the term to pretty print
     * @param linewidth length of a line, a positive number
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
     * pretty print a sequent using the currently set properties on this
     * object.
     *
     * The result is a string. It is not an {@link AnnotatedString}, no
     * character to formula information is stored.
     *
     * @param sequent the sequent to print
     * @return a string representing the sequent
     */
    public String print(Sequent sequent) {
        return print(sequent, Integer.MAX_VALUE);
    }

    /**
     * pretty print a sequent using the currently set properties on this
     * object.
     *
     * The result is a string. It is not an {@link AnnotatedString}, no
     * character to formula information is stored.
     *
     * @param sequent   the sequent to print
     * @param linewidth length of a line, a positive number
     * @return a string representing the sequent, lines are no longer than
     * linewidth
     */
    public String print(Sequent sequent, int linewidth) {
        return print(sequent, new PrettyPrintLayouter(linewidth));
    }

    /**
     * pretty print a sequent using the currently set properties on this
     * object.
     *
     * The result is a string. It is not an {@link AnnotatedString}, no
     * character to formula information is stored.
     *
     * @param sequent the sequent to print
     * @param printer the layouter to append the term to
     * @return a string representing the sequent
     */
    private String print(Sequent sequent, PrettyPrintLayouter printer) {

        PrettyPrintVisitor visitor = new PrettyPrintVisitor(this, printer);

        printer.beginBlock(0);
        printer.indentBlock(0, 3);
        boolean first = true;
        for (ProofFormula formula : sequent.getAntecedent()) {
            if (first) {
                first = false;
            } else {
                printer.append(",").breakBlock(1, 3);
            }
            formula.getTerm().accept(visitor, null);
        }

        if (!sequent.getAntecedent().isEmpty()) {
            printer.breakBlock(1, 0);
        }

        printer.append("|-");

        first = true;
        for (ProofFormula formula : sequent.getSuccedent()) {
            if (first) {
                printer.append(" ");
                first = false;
            } else {
                printer.append(",").breakBlock(1, 3);
            }
            formula.getTerm().accept(visitor, null);
        }

        printer.endBlock();

        assert printer.hasEmptyStack() :
                "Cannot render: " + sequent;

        return printer.getAnnotatedString().toString();

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

    /**
     * Find the {@link PrettyPrintExtension} responsible for printing a function
     * symbol.
     *
     * @param f the function symbol to prettyprint.
     * @return the extension that knows printing <code>f</code>, or
     * <code>null</code>
     */
    public
    @Nullable
    PrettyPrintExtension getExtensionFor(@NonNull FunctionSymbol f) {
        if (responsibleExtensions.containsKey(f)) {
            return responsibleExtensions.get(f);
        } else {
            for (PrettyPrintExtension ppe : EXTENSIONS) {
                if (ppe.canPrint(f)) {
                    responsibleExtensions.put(f, ppe);
                    return ppe;
                }
            }
            responsibleExtensions.put(f, null);
            return null;
        }
    }

    public VariablePrettyPrintExtension getVariablePrettyPrintExtension() {
        return variablePrettyPrintExtension;
    }
}
