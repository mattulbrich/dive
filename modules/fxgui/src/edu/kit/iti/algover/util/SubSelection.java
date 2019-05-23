/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.util;

import javafx.beans.property.ObjectProperty;
import javafx.beans.property.SimpleObjectProperty;

import java.util.function.Consumer;
import java.util.function.Function;

/**
 * Subselection manage a single selected datum of type S, usually something like a pointer
 * on data, for example a {@link edu.kit.iti.algover.rules.TermSelector}.
 * <p>
 * They are used, when you want to enforce that two components share a selection state, so that
 * when one component selects something, the selection on the second component disappears.
 * <p>
 * Imagine a Sequent view for example. You might want to have the selection of a formula in the
 * succedent disappear when the user selects something in the antecedent.
 * <p>
 * However, you don't want them to know about each other, so you build an encapsulating component
 * that mediates messages between them two or even stores the shared state of selection.
 * <p>
 * They are called "Sub"selections, because they can be nested again (imagine another sequent that
 * is supposed to share selection state with the first one). So usually SubSelections build up in
 * the form of a tree.
 * <p>
 * Since this pattern appeared all over my codebase, I extracted this abstraction.
 * <p>
 * For a more concrete and simple example of to use these SubSelections, see
 * {@link edu.kit.iti.algover.SubSelectionTest}.
 *
 * @param <S> something that describes the location of the selected item, for example an {@link Integer}, when selecting
 *            items of a list. Other usecases in this codebases have been
 *            {@link edu.kit.iti.algover.rules.SubtermSelector},
 *            {@link edu.kit.iti.algover.rules.TermSelector} and
 *            {@link edu.kit.iti.algover.references.ProofTermReference}.
 */
public class SubSelection<S> {

    private final ObjectProperty<S> selected;
    private final Consumer<S> onUpdateListener;

    /**
     * Create a Selection with nothing selected inside by default.
     * (<code>{@link #selected}().get()</code> would return null).
     * <p>
     * The constructor should only be used for top-level selections. If you want to derive
     * a SubSelection from an existing top-level selection, use {@link #subSelection(Function, Function)}.
     *
     * @param onUpdateListener an action that should be executed once the selection is updated.
     */
    public SubSelection(Consumer<S> onUpdateListener) {
        this((S) null, onUpdateListener);
    }

    /**
     * Create a SubSelection with given initial selection.
     * <p>
     * The constructor should only be used for top-level selections. If you want to derive
     * a SubSelection from an existing top-level selection, use {@link #subSelection(Function, Function)}.
     *
     * @param initial          the initial value the SubSelection should hold as a pointer/location of selection.
     * @param onUpdateListener an action that should be executed once the selection is updated.
     */
    public SubSelection(S initial, Consumer<S> onUpdateListener) {
        this(new SimpleObjectProperty<>(initial), onUpdateListener);
    }

    /**
     * Create a SubSelection that reuses a given ObjectProperty as selection.
     * <p>
     * The constructor should only be used for top-level selections. If you want to derive
     * a SubSelection from an existing top-level selection, use {@link #subSelection(Function, Function)}.
     *
     * @param selected         object property to reuse for storing the selected item
     * @param onUpdateListener an action that should be executed once the selection is updated
     */
    public SubSelection(ObjectProperty<S> selected, Consumer<S> onUpdateListener) {
        this.selected = selected;
        this.onUpdateListener = onUpdateListener;
    }

    /**
     * Derive a lower-level SubSelection from a higher-level SubSelection.
     * <p>
     * Imagine a succedent and an antecedent both expecting references to <code>SubSelection&lt;SubtermSelector&gt;</code>,
     * and a top-level <code>SubSelection&lt;TermSelector&gt;</code> managed in the container for both.
     * <p>
     * You create the subselections for the antecedent and succedent by deriving it from the top-level SubSelection
     * using this method. See {@link edu.kit.iti.algover.SubSelectionTest} for a more detailed example.
     *
     * @param updateInner a function mapping higher selection pointers to lower ones. If the higher one does not
     *                    point to anything this SubSelection is supposed to manage, then it returns null (= "nothing
     *                    selected")
     * @param updateOuter a function mapping lower selection pointers to higher ones.
     * @param <Sub>       The kind of location/pointer datatype used for the selection below. So for example SubtermSelector
     *                    when deriving from a TermSelector.
     * @return the SubSelection linked into the tree of its parent.
     */
    public <Sub> SubSelection<Sub> subSelection(Function<S, Sub> updateInner, Function<Sub, S> updateOuter) {
        final Function<S, Sub> nullHandlingInner = mapNull(updateInner);
        final Function<Sub, S> nullHandlingOuter = mapNull(updateOuter);

        ObjectProperty<Sub> subProperty = BindingsUtil.convert(nullHandlingInner, selected);
        return new SubSelection<Sub>(subProperty, inner -> select(nullHandlingOuter.apply(inner)));
    }

    /**
     * Hint: don't use <code>{@link #selected()}.set(...)</code>, use {@link #select(Object)} instead.
     *
     * @return an ObjectProperty storing the selection pointer/location datatype.
     */
    public ObjectProperty<S> selected() {
        return selected;
    }

    /**
     * Select a specific location. Updates the whole selection tree.
     * <p>
     * <code>select(null)</code> will reset the selection for the whole subselection tree.
     *
     * @param s what to select
     */
    public void select(S s) {
        selected.set(s);
        onUpdateListener.accept(s);
    }

    /**
     * Will reset the selection for the whole subselection tree. Results in nothing being selected anymore,
     * not only in this subselection, but every other linked to this one as well.
     * <p>
     * Same as <code>select(null)</code>.
     */
    public void unsetGobally() {
        select(null);
    }

    private <A, R> Function<A, R> mapNull(Function<A, R> nonNullHandling) {
        return a -> a == null ? null : nonNullHandling.apply(a);
    }

}
