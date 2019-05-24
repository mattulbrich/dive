/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 *
 */
package edu.kit.iti.algover.swing;

import java.awt.*;
import java.beans.PropertyChangeListener;
import java.beans.PropertyChangeListenerProxy;
import java.beans.PropertyChangeSupport;
import java.io.File;
import java.io.IOException;
import java.net.URL;
import java.util.Collections;
import java.util.Iterator;
import java.util.List;

import javax.swing.*;

import edu.kit.iti.algover.parser.DafnyException;
import edu.kit.iti.algover.parser.DafnyParserException;
import edu.kit.iti.algover.project.Project;
import edu.kit.iti.algover.project.ProjectManager;
import edu.kit.iti.algover.swing.actions.BarManager;
import edu.kit.iti.algover.swing.util.Property;
import edu.kit.iti.algover.term.prettyprint.PrettyPrint;
import edu.kit.iti.algover.util.FormatException;
import nonnull.NonNull;
import nonnull.Nullable;

/**
 * The Class DiveCenter is the center point of one proof and its visualiation
 * across several components.
 *
 * It keeps references to UI the main window as top level gui element.
 *
 * A general PropertyChange mechanism is installed to provide an opportunity to
 * work with general properties on the proof process.
 */
public class DiveCenter {

    /**
     * Property key indicating that an automatic proof is on the run. This will
     * be set by all actions in actions.auto. <br>
     * Type: Boolean
     */
    public final Property<Boolean> onGoingProof =
            new Property<>("onGoingProof", Boolean.class, true);

    /**
     * There are 3 viewports and they can be switched
     */
    public final Property<Viewport> viewPort =
            new Property<>("viewPort", Viewport.class, null);

    public final Property<Project> project =
            new Property<>("project", Project.class, null);

    public final Property<Boolean> terminated =
            new Property<>("terminated", Boolean.class, false);

    /**
     * Property key to indicate that a proof node has been selected.
     * Type: ProofNode
     */
    public static final String SELECTED_PROOFNODE = "pseudo.selectedProofNode";

    /**
     * Property key to indicate that a rule application has been selected.
     * Type: RuleApplication
     */
    public static final String SELECTED_RULEAPPLICATION = "pseudo.selectedRuleApplication";

    /**
     * Property key to denote the verbosity of the display Type: int
     */
    public static final String TREE_VERBOSITY = "pseudo.tree.verbosity";

    /**
     * Property key to denote whether numbers should be printed in display Type:
     * boolean
     */
    public static final String TREE_SHOW_NUMBERS = "pseudo.tree.shownumbers";

    /**
     * Property key to denote whether program traces should be highlighted or
     * not<br>
     * Type: boolean
     */
    public static final String CODE_PANE_SHOW_TRACE = "pseudo.program.showtrace";

    /**
     * Notification signal to indicate that a node in the proof has been
     * changed. Activated every time that the proof is changed (observing the
     * proof)<br>
     *
     * Type: {@literal List<ProofNode>}
     */
    public static final String PROOFNODES_HAVE_CHANGED = "pseudo.proofnode_changed";

    /**
     * Notification signal to indicate that the proof has changed. This is
     * called after an action on the proof has finished. This notification may
     * come after 0, 1 or several proof node changes to the proof.
     */
    public static final String PROOFTREE_HAS_CHANGED = "pseudo.prooftree_changed";

    /**
     * Notification signal to indicate that an ongoing action is to be stopped.
     * Typically thrown when pressing the proof button in "stop" mode.
     */
    public static final String STOP_REQUEST = "pseudo.stop_request";

    /**
     * Notification signal to indicate that this proof center has reached the end
     * of its live cycle. Resources should be freed.
     */
    public static final String TERMINATION = "pseudo.termination";

    /**
     * The controller of the mainframe. Allows accessing all other controllers.
     */
    private final MainController mainController;

    /**
     * The currently showed project.
     *
     * This may be null if not parsable or after invalidation.
     */
    private final ProjectManager projectManager;

    /**
     * the system pretty printer used by components, configured by menu
     */
    private final PrettyPrint prettyPrinter;

    /**
     * Instantiates a new DIVE center.
     */
    public DiveCenter(File file)
            throws IOException, FormatException, DafnyParserException {
        this.projectManager = ProjectManager.fromFile(file);
        this.prettyPrinter = new PrettyPrint();

        mainController = new MainController(this, file.getName());
        mainController.makeGUI();

        onGoingProof.setValueOnEventQueue(false);
    }

    public void activate() {
        try {
            viewPort.setValue(Viewport.PVC_VIEW);
            projectManager.reload();

            // TODO EXC!
        } catch (DafnyException e) {
            e.printStackTrace();
        } catch (DafnyParserException e) {
            e.printStackTrace();
        } catch (IOException e) {
            e.printStackTrace();
        } catch (FormatException e) {
            e.printStackTrace();
        }
        getMainWindow().setVisible(true);
    }

    /**
     * Gets the main window.
     *
     * @return the main window
     */
    public JFrame getMainWindow() {
        return mainController.getFrame();
    }

    /**
     * Gets the main controller (which controls the main window).
     *
     * @return the main controller
     */
    public @NonNull MainController getMainController() {
        return mainController;
    }

    /**
     * Gets the bar manager of the main window.
     *
     * The bar manager is responsible for the menu bar and tool bar.
     *
     * @see BarManager
     *
     * @return the bar manager
     */
    public BarManager getBarManager() {
        return getMainController().getBarManager();
    }

    public boolean hasUnsafedChanges() {
        return true;
    }

//    /**
//     * Indicate that a proof node has been selected.
//     *
//     * All registered proof node selection listeners are informed of this
//     * selection. The notification is ensured to be run on the swing event queue
//     * thread. It may or may not have already been executed when this method
//     * returns.
//     *
//     * This method will fire a change, even if the same node has been selected,
//     * so listeners must not invoke this method.
//     *
//     * @param node
//     *            the node to be selected
//     */
//    public void fireSelectedProofNode(@NonNull ProofNode node) {
//        firePropertyChange(SELECTED_PROOFNODE, node);
//    }
//
//    /**
//     * Indicate that a proof step has been completed and the tree should be
//     * reassessed.
//     *
//     * All registered notification listeners listening to the signal
//     * {@link DiveCenter#PROOFTREE_HAS_CHANGED} will get notified.
//     *
//     * @param selectNextGoal
//     *            if this is true, the next selectable goal is automatically
//     *            selected.
//     */
//    public void fireProoftreeChangedNotification(final boolean selectNextGoal) {
//        fireNotification(PROOFTREE_HAS_CHANGED);
//        if (selectNextGoal) {
//            selectNextGoal();
//        }
//    }
//
//    /**
//     * Gets the List of possible rule applications for a term within the
//     * currently selected proof node. The term is given by its selector.
//     *
//     * <P>
//     * A list of all possible rule applications which match against a rule which
//     * is not marked automatic-only.
//     *
//     * @param termSelector
//     *            the reference of the selected term.
//     *
//     * @return a list of rule applications that match the selected term
//     *
//     * @throws ProofException
//     */
//    public @NonNull List<RuleApplication> getApplicableRules(@NonNull TermSelector termSelector) throws ProofException {
//
//        Log.enter(termSelector);
//
//        ProofNode node = getCurrentProofNode();
//        RuleApplicationFinder iraf = new RuleApplicationFinder(node, env);
//        List<RuleApplication> result = iraf.findAll(termSelector, rulesSortedForInteraction);
//
//        Log.log(Log.VERBOSE, "Found rule apps: " + result);
//        return result;
//    }
//
//    /**
//     * Apply a rule application to the proof.
//     *
//     * The call is basically delegated to the proof itself. However, afterwards,
//     * in case of a successful application, a sensible node is selected
//     * automatically. This is: The target node itself if it is still a goal, or
//     * the first child goal of the target of there is any, or the first
//     * remaining goal of the entire sequent if there is any or the root node if
//     * the proof is closed.
//     *
//     * <p>
//     * The method returns the next open goal. If the application created open
//     * nodes, the first one will be returned. If the application closed the
//     * branch, the first open goal will be returned. If the whole tree is
//     * closed, the root is returned - though not an open goal.
//     *
//     * @param ruleApp
//     *            the rule application to apply onto the proof.
//     *
//     * @throws ProofException
//     *             if the application fails.
//     */
//    public void apply(RuleApplication ruleApp) throws ProofException {
//        Log.enter(ruleApp);
//        proof.apply(ruleApp);
//    }
//
//    /**
//     * Prune a proof.
//     *
//     * This is delegated to the proof object. On success, the change of the
//     * proof structure is propagated by a notification of the signal
//     * {@value #PROOFTREE_HAS_CHANGED}.
//     *
//     * @param proofNode
//     *            the node in the proof to prune.
//     * @throws ProofException
//     *             if the node is not part of this proof.
//     */
//    public void prune(ProofNode proofNode) throws ProofException {
//        proof.prune(proofNode);
//    }
//
//    /**
//     * Gets the currently selected proof node.
//     *
//     * @return the currently selected proof node
//     */
//    public @Nullable ProofNode getCurrentProofNode() {
//        Object currentPN = getProperty(SELECTED_PROOFNODE);
//        return (currentPN instanceof ProofNode) ? (ProofNode) currentPN : null;
//    }
//
//
//
//    /**
//     * Get the pretty printer for this proof surrounding. The printer can be
//     * changed via menu entries. You can add a {@link PropertyChangeListener} if
//     * you want to be informed about changes.
//     *
//     * @return the system pretty printer;
//     */
//    public PrettyPrint getPrettyPrinter() {
//        return prettyPrinter;
//    }
//
//    /**
//     * Get the strategy manager for this proof surrounding.
//     *
//     * @return the system strategy manager
//     */
//    public @NonNull StrategyManager getStrategyManager() {
//        return strategyManager;
//    }
//
//    /**
//     * get the BreakpointManager for the surrounding.
//     *
//     * The BreakpointManager is not necessarily part of the system. This will
//     * fail if {@link BreakpointStrategy} is not available since this class is
//     * asked to provide that instance.
//     *
//     * <p>
//     * We cannot keep the instance here because the strategies are part of the
//     * core system and cannot access proof centers.
//     *
//     * @return the breakpoint manager of the {@link BreakpointStrategy}.
//     * @throws StrategyException
//     *             if the breakpoint strategy is not available
//     * @see BreakpointStrategy#getBreakpointManager()
//     */
//    public BreakpointManager getBreakpointManager() throws StrategyException {
//        return getStrategyManager().getStrategy(BreakpointStrategy.class).getBreakpointManager();
//    }
//
//    // Delegations to changeSupport!
//
//    /**
//     * Adds a listener loooking for a certain kind of changes.
//     *
//     * @see PropertyChangeSupport#addPropertyChangeListener(String,
//     *      PropertyChangeListener)
//     *
//     * @param propertyName
//     *            the property to look out for
//     * @param listener
//     *            the listener to handle changes
//     */
//    public void addPropertyChangeListener(String propertyName, PropertyChangeListener listener) {
//        Log.enter(propertyName, listener);
//        changeSupport.addPropertyChangeListener(propertyName, listener);
//    }
//
//    /**
//     * Adds a listener listening to a a certain kind of notification.
//     *
//     * @see NotificationSupport#addNotificationListener(String, NotificationListener)
//     *
//     * @param signal
//     *            the notification signal
//     * @param listener
//     *            the listener to handle signals
//     */
//    public void addNotificationListener(String signal, NotificationListener listener) {
//        Log.enter(signal, listener);
//        notificationSupport.addNotificationListener(signal, listener);
//    }
//
//    /**
//     * Notify all registered listeners that a property's value has changed.
//     *
//     * <p>
//     * Please note that an event is only triggered if the new value differs from
//     * the originally set value.
//     *
//     * @see PropertyChangeSupport#firePropertyChange(String, Object, Object)
//     *
//     * @param propertyName
//     *            name of the property
//     * @param newValue
//     *            value after the change.
//     */
//    public void firePropertyChange(String propertyName, Object newValue) {
//        // assert SwingUtilities.isEventDispatchThread();
//
//        Object oldValue = generalProperties.get(propertyName);
//        Log.log("Changing " + propertyName + " from " + oldValue + " to " + newValue);
//        generalProperties.put(propertyName, newValue);
//        changeSupport.firePropertyChange(propertyName, oldValue, newValue);
//    }

//    /**
//     * Notify all registered listeners that a property's value has changed.
//     *
//     * <p>
//     * Please note that an event is only triggered if the new value differs from
//     * the originally set value.
//     *
//     * @see PropertyChangeSupport#firePropertyChange(String, Object, Object)
//     *
//     * @param propertyName
//     *            name of the property
//     * @param newValue
//     *            value after the change.
//     * @param oldValue
//     *            value that will be send as oldValue
//     */
//    public void firePropertyChange(String propertyName, Object newValue, Object oldValue) {
//        assert SwingUtilities.isEventDispatchThread();
//
//        Log.log("Changing " + propertyName + " from " + oldValue + " to " + newValue);
//        generalProperties.put(propertyName, newValue);
//        changeSupport.firePropertyChange(propertyName, oldValue, newValue);
//    }

//    /**
//     * Notify all registered listeners that a property's value has been set.
//     *
//     * <p>
//     * Please note that an event is triggered even if no <b>new</b> value is set
//     * but rather the old value repeated. Setting a value of <code>null</code>
//     * however, does not trigger an event.
//     *
//     * @see PropertyChangeSupport#firePropertyChange(String, Object, Object)
//     *
//     * @param propertyName
//     *            name of the property
//     * @param newValue
//     *            value after the change.
//     */
//    public void fireNotification(String signal, Object... parameters) {
//        assert SwingUtilities.isEventDispatchThread();
//        Log.enter(signal, Util.readOnlyArrayList(parameters));
//        notificationSupport.fireNotification(signal, parameters);
//    }
//
//    /**
//     * Gets the value of a property.
//     *
//     * @param propertyName
//     *            the property name
//     *
//     * @return the property's value. null if not set
//     */
//    public @Nullable Object getProperty(String propertyName) {
//        return generalProperties.get(propertyName);
//    }
//
//    /**
//     * Removes a listener loooking for a certain kind of changes.
//     *
//     * @see PropertyChangeSupport#removePropertyChangeListener(String,
//     *      PropertyChangeListener)
//     *
//     * @param propertyName
//     *            the property to look out for
//     * @param listener
//     *            the listener to handle changes
//     */
//    public void removePropertyChangeListener(String propertyName, PropertyChangeListener listener) {
//        changeSupport.removePropertyChangeListener(propertyName, listener);
//    }
//
//    public void removeNotificationListener(String signal, NotificationListener listener) {
//        notificationSupport.removeNotificationListener(signal, listener);
//    }
//
//    /**
//     * This method prints all registered {@link PropertyChangeListener}s to
//     * System.err. It is solely for debug purposes.
//     */
//    public void dumpPropertyListeners() {
//        PropertyChangeListener[] listeners = changeSupport.getPropertyChangeListeners();
//        for (PropertyChangeListener listener : listeners) {
//            if (listener instanceof PropertyChangeListenerProxy) {
//                PropertyChangeListenerProxy proxy = (PropertyChangeListenerProxy) listener;
//                System.err.println(proxy.getPropertyName() + ": " + proxy.getListener());
//            } else {
//                System.err.println("*: " + listener);
//            }
//        }
//
//    }
//
//    private void selectNextGoal() {
//        ProofNode res = findGoal(getCurrentProofNode());
//
//        if (res == null) {
//            res = findGoal(proof.getRoot());
//        }
//
//        if (res == null) {
//            Log.log(Log.DEBUG, "No goal to select, selected root");
//            fireSelectedProofNode(proof.getRoot());
//        } else {
//            Log.log(Log.DEBUG, "Goal selected: " + res);
//            fireSelectedProofNode(res);
//        }
//    }
//
//    private ProofNode findGoal(ProofNode p) {
//        if (p.getChildren() == null) {
//            return p;
//        }
//
//        for (ProofNode pn : p.getChildren()) {
//            ProofNode res = findGoal(pn);
//            if (res != null) {
//                return res;
//            }
//        }
//
//        return null;
//    }


}
