///*
// * This file is part of AlgoVer.
// *
// * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
// *
// */
//package edu.kit.iti.algover.swing.sequent;
//
//import java.awt.Component;
//import java.awt.MouseInfo;
//import java.awt.Point;
//import java.awt.datatransfer.DataFlavor;
//import java.awt.datatransfer.StringSelection;
//import java.awt.datatransfer.Transferable;
//import java.awt.event.ActionEvent;
//import java.awt.event.ActionListener;
//import java.util.ArrayList;
//import java.util.LinkedList;
//import java.util.List;
//import java.util.Map;
//
//import javax.swing.JComponent;
//import javax.swing.JMenuItem;
//import javax.swing.JPopupMenu;
//import javax.swing.SwingUtilities;
//import javax.swing.TransferHandler;
//import javax.swing.text.JTextComponent;
//
//import edu.kit.iti.algover.swing.util.Log;
//
///**
// * This class implements string based drag and drop for TermComponent. This
// * allows for fast interactive rule applications by dropping terms from
// * TermComponents or unformatted text from other applications such as text
// * editors.
// *
// * @author timm.felden@felden.com
// */
//public class TermSelectionTransfer extends TransferHandler {
//
//    private static final long serialVersionUID = -1292983185215324664L;
//    private static final TransferHandler instance = new TermSelectionTransfer();
//
//    /**
//     * The transfer handler has no state and is therefore thread safe and can be
//     * used as singleton.
//     */
//    private TermSelectionTransfer() {
//    }
//
//    @Override
//    public int getSourceActions(JComponent c) {
//        Log.enter(c);
//        return COPY;
//    }
//
//    @Override
//    protected Transferable createTransferable(JComponent c) {
//        Log.enter(c);
//        if (c instanceof TermComponent) {
//            TermComponent tc = (TermComponent) c;
//            return tc.createTransferable();
//        } else if (c instanceof JTextComponent) {
//            return new StringSelection(((JTextComponent) c).getText());
//        }
//
//        return null;
//    }
//
//    @Override
//    public boolean importData(TransferSupport support) {
//        Log.enter(support);
//        try {
//            Component c = support.getComponent();
//            Transferable t = support.getTransferable();
//            if (c instanceof TermComponent) {
//                TermComponent tc = (TermComponent) c;
//
//                // disable drops on closed proof nodes
//                if (null != tc.getProofCenter().getCurrentProofNode().getChildren()) {
//                    return false;
//                }
//
//                return dropOnTermComponent(tc, support);
//            } else if (c instanceof JTextComponent) {
//                String text = (String) t.getTransferData(DataFlavor.stringFlavor);
//                // MU replaced
//                // ((JTextComponent) c).setText(text);
//                ((JTextComponent)c).replaceSelection(text);
//                return true;
//            }
//        } catch (Exception e) {
//            e.printStackTrace();
//        } finally {
//            Log.leave();
//        }
//        return false;
//    }
//
//    @Override
//    public boolean canImport(TransferSupport support) {
//
//        if (support.getTransferable() instanceof TermSelectionTransferable) {
//            return true;
//        }
//
//        return support.isDataFlavorSupported(DataFlavor.stringFlavor);
//    }
//
//    public static TransferHandler getInstance() {
//        return instance;
//    }
//
//
//    // /////////// RULE APPLICATION CODE /////////////////// //
//
//
//    /**
//     * try to drop the term in support on target
//     */
//    private boolean dropOnTermComponent(final TermComponent target, final TransferSupport support) {
//
//        final ProofCenter pc = target.getProofCenter();
//
//        Term transferedTerm;
//        TermSelector location = null;
//        try {
//            if (!support.isDataFlavorSupported(TermSelectionTransferable.TERM_DATA_FLAVOR)) {
//                // Is this the right node for locals?
//                SymbolTable symbols = pc.getCurrentProofNode().getLocalSymbolTable();
//                transferedTerm = TermMaker.makeAndTypeTerm((String) support.getTransferable().getTransferData(
//                        DataFlavor.stringFlavor), symbols);
//
//            } else {
//                TermSelectionTransferable ts = (TermSelectionTransferable) support.getTransferable().getTransferData(
//                        TermSelectionTransferable.TERM_DATA_FLAVOR);
//
//                transferedTerm = ts.getSelector().selectSubterm(pc.getCurrentProofNode().getSequent());
//
//                // the location can only be used if both terms belong to the
//                // same proof
//                if (target.getProofCenter() == ts.getSource().getProofCenter()) {
//                    location = ts.getSelector();
//                }
//            }
//        } catch (Exception e) {
//            // if an exception occurs here, the dropped text is not a term
//
//            // this behavior is needed to allow terms to be dragged out of
//            // other applications such as browsers or document viewers
//            return false;
//        }
//
//        try {
//            // find applications
//            final List<List<RuleApplication>> buckets = findRulesApplicable(transferedTerm, location, target,
//                    pc);
//
//            // select applications
//            return applyBestRule(buckets, target, pc);
//
//        } catch (Exception e) {
//            ExceptionDialog.showExceptionDialog(pc.getMainWindow(), e);
//            return false;
//        }
//    }
//
//    /**
//     * Try to find all applicable rules with a dragdrop tag.
//     *
//     * <p>
//     * If the Term is not located on the ProofNode(iff location == null), try to
//     * find only rules that can be used with drag and drop and are
//     * <b>interactive</b>, because non-interactive drag and drop rules assume
//     * the dropped term, which can not be done without the knowledge of the
//     * location of the source term. Fortunately prohibited by the core, this
//     * would enable the user to assume arbitrary terms by dragging them from a
//     * source such as a text editor.
//     */
//    private List<List<RuleApplication>> findRulesApplicable(final Term transferedTerm,
//            final TermSelector location,
//            TermComponent target, final ProofCenter proofCenter) throws ProofException {
//
//        final Environment env = proofCenter.getEnvironment();
//
//        // if we can apply a rule using drap and drop, we can also apply the
//        // same rule without drag and drop, so it is enaugh to find all
//        // applicable rules and filter them
//        final List<RuleApplication> rulesApplicable = target.getApplicableRules();
//
//        // buckets for priority 0 - 9
//        List<List<RuleApplication>> bucket = new ArrayList<List<RuleApplication>>(10);
//        for (int i = 0; i < 10; i++) {
//            bucket.add(new ArrayList<RuleApplication>(3));
//        }
//
//        // filter rules
//        for (RuleApplication ra : rulesApplicable) {
//            SymbolTable local = ra.getProofNode().getLocalSymbolTable();
//            final String level = ra.getRule().getProperty("dragdrop");
//            if (null == level) {
//                continue;
//            }
//
//            int lvl = Integer.parseInt(level);
//            boolean isInteractive = false;
//
//            // set the interactive field to match instantiation
//            for (Map.Entry<String, String> entry : ra.getProperties().entrySet()) {
//                String key = entry.getKey();
//                if (!key.startsWith(Interactive.INTERACTION + "(")) {
//                    continue;
//                }
//
//                String value = entry.getValue();
//                boolean typeMode = false;
//
//                if (value.startsWith(Interactive.INSTANTIATE_PREFIX)) {
//                    typeMode = true;
//                    value = value.substring(Interactive.INSTANTIATE_PREFIX.length());
//                }
//
//                String svName = Util.stripQuotes(key.substring(Interactive.INTERACTION.length()));
//                Type svType;
//                try {
//                    svType = TermMaker.makeType(value, local);
//                } catch (ASTVisitException e) {
//                    Log.log(Log.WARNING, "cannot parseType: " + value + ", continue anyway");
//                    continue;
//                } catch (ParseException e) {
//                    Log.log(Log.WARNING, "cannot parseType: " + value + ", continue anyway");
//                    continue;
//                }
//
//                ra = new MutableRuleApplication(ra);
//
//                ra.getSchemaVariableMapping().put(svName, transferedTerm);
//                if (typeMode) {
//                    ra.getTypeVariableMapping().put(((SchemaType) svType).getVariableName(), transferedTerm.getType());
//                }
//
//                // only allow rules with one interaction
//                isInteractive = true;
//                break;
//            }
//            // we have to ensure, that the rule has only one assume clause and
//            // we have to replace this clause
//            if (!isInteractive){
//                // the drag originated not from our proof
//                if (null == location) {
//                    continue;
//                }
//
//                if (ra.getRule().getAssumptions().size() != 1) {
//                    Log.log(Log.ERROR, "The rule " + ra.getRule() + " is illformed respective to the 'dragdrop' tag!");
//                    continue;
//                }
//                // the assumption has to be the one we dragged, or the
//                // application is not interesting
//                if (!ra.getAssumeSelectors().get(0).equals(location)) {
//                    continue;
//                }
//            }
//
//            RuleApplicationCertificate cert = new RuleApplicationCertificate(ra, env);
//            // check if ra is still applicable
//            // it is checked now and needs not be checked again.
//            if (!ra.getProofNode().applicable(cert)) {
//                continue;
//            }
//
//            // adjust level; if level is invalid, map it to 0
//            lvl = lvl > 0 && lvl < 10 ? lvl : 0;
//            bucket.get(lvl).add(cert);
//        }
//
//        return bucket;
//    }
//
//    /**
//     * tries to apply the rule that the user is most interested in; if the rule
//     * can not be found without asking the user, a pop-up will be displayed.
//     */
//    private boolean applyBestRule(final List<List<RuleApplication>> buckets, final TermComponent tc,
//            final ProofCenter proofCenter) throws ProofException {
//        final LinkedList<RuleApplication> ruleApps = new LinkedList<RuleApplication>();
//
//        // the user might have specified, that he wants always the rule in
//        // the highest bucket to be applied
//        {
//            boolean highestOnly = (Boolean) proofCenter.getProperty(TermComponent.HIGHEST_PRIORITY_DRAG_AND_DROP);
//            for (int i = 9; i >= 0; i--) {
//                ruleApps.addAll(buckets.get(i));
//
//                if (highestOnly && !ruleApps.isEmpty()) {
//                    break;
//                }
//            }
//        }
//
//        // if no rules are applicable, the drop failed
//        if (ruleApps.size() == 0) {
//            return false;
//        }
//
//        // only one rule is applicable, so apply it
//        if (ruleApps.size() == 1) {
//            finishApplication(ruleApps.get(0), proofCenter);
//            return true;
//        }
//
//        // we don't know which rule to select, so let the user decide what
//        // he wants
//        {
//            final JPopupMenu popup = new JPopupMenu();
//
//            ActionListener listener = new ActionListener() {
//                @Override
//                public void actionPerformed(ActionEvent e) {
//                    popup.setVisible(false);
//
//                    final String rule = ((JMenuItem) e.getSource()).getText();
//
//                    // we have to search the rule with the same name as
//                    // rule, but this is not a problem, as in general, there
//                    // are only few rules applicable
//
//                    for (RuleApplication ra : ruleApps) {
//                        if (ra.getRule().getName().equals(rule)) {
//                            try {
//                                finishApplication(ra, proofCenter);
//                            } catch (ProofException e1) {
//                                ExceptionDialog.showExceptionDialog(proofCenter.getMainWindow(), e1);
//                            }
//                            return;
//                        }
//                    }
//                }
//            };
//
//            for (RuleApplication ra : ruleApps) {
//                popup.add(ra.getRule().getName()).addActionListener(listener);
//            }
//
//            Point p = MouseInfo.getPointerInfo().getLocation();
//            SwingUtilities.convertPointFromScreen(p, tc);
//            popup.show(tc, p.x, p.y);
//
//            // in this case, the event is created by the action listener
//            return true;
//        }
//    }
//
//    /**
//     * select the most interesting node
//     *
//     * @param target
//     *            node which was used to apply the drop action
//     * @param pc
//     *            the ProofCenter used by the drop location
//     */
//    private void finishApplication(RuleApplication ra, ProofCenter pc) throws ProofException {
//
//        ra = new MutableRuleApplication(ra);
//        ra.getProperties().put(InteractiveRuleApplicationComponent.MANUAL_RULEAPP, "true");
//        pc.apply(ra);
//
//        final ProofNode target = pc.getCurrentProofNode();
//
//        if (target.getChildren().size() > 0) {
//            pc.fireSelectedProofNode(target.getChildren().get(0));
//        } else if (pc.getProof().hasOpenGoals()) {
//            pc.fireSelectedProofNode(pc.getProof().getGoalByNumber(0));
//        } else {
//            pc.fireSelectedProofNode(pc.getProof().getRoot());
//        }
//    }
//}
