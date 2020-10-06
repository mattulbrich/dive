///*
// * This file is part of AlgoVer.
// *
// * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
// *
// */
//package edu.kit.iti.algover.swing.sequent;
//
//import java.awt.Color;
//import java.awt.Component;
//import java.awt.Container;
//import java.awt.Dimension;
//import java.awt.Graphics;
//import java.awt.Insets;
//import java.awt.LayoutManager;
//import java.awt.Rectangle;
//import java.awt.event.MouseAdapter;
//import java.awt.event.MouseEvent;
//import java.awt.event.MouseListener;
//import java.beans.PropertyChangeEvent;
//import java.beans.PropertyChangeListener;
//import java.util.List;
//
//import javax.swing.JPanel;
//import javax.swing.Scrollable;
//import javax.swing.SwingUtilities;
//
//import nonnull.NonNull;
//import de.uka.iti.pseudo.gui.ProofCenter;
//import de.uka.iti.pseudo.prettyprint.PrettyPrint;
//import de.uka.iti.pseudo.proof.ProofException;
//import de.uka.iti.pseudo.proof.ProofNode;
//import de.uka.iti.pseudo.proof.RuleApplication;
//import de.uka.iti.pseudo.proof.SequentHistory;
//import de.uka.iti.pseudo.proof.TermSelector;
//import de.uka.iti.pseudo.proof.SequentHistory.Annotation;
//import de.uka.iti.pseudo.term.Sequent;
//import de.uka.iti.pseudo.term.Term;
//import de.uka.iti.pseudo.util.ExceptionDialog;
//import de.uka.iti.pseudo.util.NotificationEvent;
//import de.uka.iti.pseudo.util.NotificationListener;
//import de.uka.iti.pseudo.util.settings.Settings;
//
//// TODO DOC
//
//public class SequentComponent extends JPanel implements Scrollable {
//
//    private static final long serialVersionUID = -3882151273674917147L;
//
//    private static final String SETTINGS_BACKGROUND = "pseudo.sequentview.background";
//    private static final String SETTINGS_BLOCK_INCREMENT = "pseudo.sequentview.scroll.blockIncrement";
//    private static final String SETTINGS_UNIT_INCREMENT = "pseudo.sequentview.scroll.unitIncrement";
//
//    private Separator separator = new Separator();
//    private ProofNode proofNode;
//    private boolean open;
//    private ProofCenter proofCenter;
//    private PrettyPrint prettyPrinter;
//
//
//    public SequentComponent(@NonNull ProofCenter proofCenter) {
//        proofCenter.getEnvironment();
//        this.proofCenter = proofCenter;
//        this.setLayout(new Layout());
//        prettyPrinter = proofCenter.getPrettyPrinter();
//        prettyPrinter.addPropertyChangeListener(this);
//
//        setBackground(Settings.getInstance().getColor(SETTINGS_BACKGROUND, Color.WHITE));
//    }
//
//    private void setProofNode(ProofNode proofNode, boolean open) {
//        this.proofNode = proofNode;
//        this.open = open;
//
//        Sequent sequent = proofNode.getSequent();
//        SequentHistory history = proofNode.getSequentHistory();
//
//        this.removeAll();
//
//        int i = 0;
//        for (Term t : sequent.getAntecedent()) {
//            TermSelector termSelector = new TermSelector(TermSelector.ANTECEDENT, i);
//            Annotation annotation = history.select(termSelector);
//            TermComponent termComp = new TermComponent(t, annotation, open, proofCenter, termSelector);
//            termComp.addMouseListener(termMouseListener);
//            add(termComp);
//            i++;
//        }
//
//        add(separator);
//
//        i = 0;
//        for (Term t : sequent.getSuccedent()) {
//            TermSelector termSelector = new TermSelector(TermSelector.SUCCEDENT, i);
//            Annotation annotation = history.select(termSelector);
//            TermComponent termComp = new TermComponent(t, annotation, open, proofCenter, termSelector);
//            termComp.addMouseListener(termMouseListener);
//            add(termComp);
//            i++;
//        }
//
//        revalidate();
//        repaint();
//
//    }
//
//
//
//    public void markTerm(TermSelector selector, int type) {
//
//        assert selector != null;
//
//        if(proofNode == null)
//            return;
//
//        TermComponent termComp;
//        if(selector.isAntecedent()) {
//            termComp = (TermComponent) getComponent(selector.getTermNo());
//        } else {
//            // need to jump over antecedent and separator
//            int offset = proofNode.getSequent().getAntecedent().size() + 1;
//            termComp = (TermComponent) getComponent(offset + selector.getTermNo());
//        }
//
//        termComp.markSubterm(selector.getSubtermSelector(), type);
//    }
//
//    private void ruleApplicationSelected(RuleApplication ruleApplication) {
//        //
//        // clear all previous markings on the term components
//        for (int i = 0; i < getComponentCount(); i++) {
//            Component c = getComponent(i);
//            if (c instanceof TermComponent) {
//                TermComponent termComponent = (TermComponent) c;
//                termComponent.clearMarks();
//            }
//        }
//
//        // null indicates that nothing is to be highlighted
//        if(ruleApplication != null) {
//
//            // set the current markings
//            TermSelector findSelector = ruleApplication.getFindSelector();
//            // might be a rule w/o find clause
//            if(findSelector != null) {
//                markTerm(findSelector, 0);
//            }
//            for (TermSelector sel : ruleApplication.getAssumeSelectors()) {
//                markTerm(sel, 1);
//            }
//        }
//    }
//
//    public void propertyChange(PropertyChangeEvent evt) {
//        if(evt.getSource() == prettyPrinter) {
//            setProofNode(proofNode, open);
//
//        } else if(ProofCenter.SELECTED_PROOFNODE.equals(evt.getPropertyName())) {
//            ProofNode node = (ProofNode) evt.getNewValue();
//
//            setProofNode(node, node.getChildren() == null);
//            RuleApplication ruleApp = node.getAppliedRuleApp();
//            if(ruleApp != null)
//                ruleApplicationSelected(ruleApp);
//
//        } else if(ProofCenter.SELECTED_RULEAPPLICATION.equals(evt.getPropertyName())) {
//            RuleApplication ruleApp = (RuleApplication) evt.getNewValue();
//            ruleApplicationSelected(ruleApp);
//        }
//    }
//
//    @Override
//    public void handleNotification(NotificationEvent evt) {
//        assert evt.isSignal(ProofCenter.PROOFTREE_HAS_CHANGED);
//
//        boolean open = proofNode.getChildren() == null;
//        setProofNode(proofNode, open);
//        // a node may have become closed or open
//    }
//
//    protected ProofCenter getProofCenter() {
//        return null;
//    }
//
//    // the listener that launches and makes the rule popup
//    private MouseListener termMouseListener = new MouseAdapter() {
//
//        @Override
//        public void mouseClicked(MouseEvent e) {
//
//            if (SwingUtilities.isLeftMouseButton(e) && !proofCenter.getCurrentProofNode().isClosed()
//                    && !(Boolean) proofCenter.getProperty(ProofCenter.ONGOING_PROOF)) {
//                try {
//                    TermComponent tc = (TermComponent) e.getSource();
//                    TermSelector termSelector = tc.getTermAt(e.getPoint());
//                    // System.out.println("Mouse selected: " + termSelector);
//
//                    if(termSelector == null)
//                        return;
//
//                    List<RuleApplication> ruleApps = proofCenter.getApplicableRules(termSelector);
//
//                    new InteractiveRuleApplicationPopup(proofCenter, ruleApps,
//                            e.getLocationOnScreen()).setVisible(true);
//
//                } catch (ProofException ex) {
//                    ExceptionDialog.showExceptionDialog(proofCenter.getMainWindow(), ex);
//                }
//            }
//        }
//    };
//
//
//    // -------
//    // Scrollable interface
//
//    /*
//     * return the preferred size of the component if it is high enough.
//     * Stretch it to fit into the container if needed.
//     */
//    @Override
//    public Dimension getPreferredScrollableViewportSize() {
//        // silently assume that!
//        assert getParent() != null;
//
//        Dimension d = getPreferredSize();
//        //return new Dimension(d.width, Math.max(getParent().getHeight(), d.height));
//        return d;
//    }
//
//    @Override
//    public int getScrollableBlockIncrement(Rectangle visibleRect,
//            int orientation, int direction) {
//        return Settings.getInstance().getInteger(SETTINGS_BLOCK_INCREMENT, 20);
//    }
//
//    @Override
//    public int getScrollableUnitIncrement(Rectangle visibleRect,
//            int orientation, int direction) {
//        return Settings.getInstance().getInteger(SETTINGS_UNIT_INCREMENT, 10);
//    }
//
//    /*
//     * Do vertical scrolling
//     */
//    @Override
//    public boolean getScrollableTracksViewportHeight() {
//        return false;
//    }
//
//    /*
//     * No horizontal scrolling!
//     */
//    @Override public boolean getScrollableTracksViewportWidth() {
//        return true;
//    }
//
//}
