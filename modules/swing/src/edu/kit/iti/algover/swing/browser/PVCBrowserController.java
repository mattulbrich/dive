/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 *
 */

package edu.kit.iti.algover.swing.browser;

import edu.kit.iti.algover.dafnystructures.DafnyDecl;
import edu.kit.iti.algover.parser.DafnyParser;
import edu.kit.iti.algover.parser.DafnyTree;
import edu.kit.iti.algover.project.Project;
import edu.kit.iti.algover.proof.PVC;
import edu.kit.iti.algover.proof.PVCCollection;
import edu.kit.iti.algover.proof.PVCGroup;
import edu.kit.iti.algover.proof.Proof;
import edu.kit.iti.algover.proof.ProofStatus;
import edu.kit.iti.algover.proof.SinglePVC;
import edu.kit.iti.algover.swing.DiveCenter;
import edu.kit.iti.algover.swing.Viewport;

import javax.swing.*;
import javax.swing.event.TreeSelectionEvent;
import javax.swing.text.View;
import javax.swing.tree.DefaultMutableTreeNode;
import javax.swing.tree.DefaultTreeModel;
import javax.swing.tree.TreePath;
import java.awt.*;
import java.awt.event.MouseAdapter;
import java.awt.event.MouseEvent;
import java.awt.event.MouseListener;
import java.util.List;

public class PVCBrowserController {

    private final DiveCenter diveCenter;
    private final JScrollPane theComponent;
    private final JTree tree;

    private final MouseListener doubleClickListener = new MouseAdapter() {
        @Override
        public void mouseClicked(MouseEvent e) {
            Object sel = tree.getLastSelectedPathComponent();
            if(sel instanceof TreeNode && ((TreeNode)sel).getChildCount() > 0) {
                return;
            }

            if (SwingUtilities.isLeftMouseButton(e) && e.getClickCount() == 2) {
                Viewport viewport;
                if ((e.getModifiersEx() & MouseEvent.SHIFT_DOWN_MASK) != 0) {
                    viewport = Viewport.PROOF_VIEW;
                } else {
                    viewport = Viewport.CODE_VIEW;
                }
                diveCenter.properties().viewPort.setValue(viewport);
            }
        }
    };

    public class TreeNode extends DefaultMutableTreeNode {

        private final PVCCollection pvcCollection;

        private final String type;
        private final String name;
        private final int countAllPVC;

        private int countFinishedPVCs;

        public String getType() {
            return type;
        }

        public String getName() {
            return name;
        }

        public int getCountAllPVC() {
            return countAllPVC;
        }

        public int getCountFinishedPVCs() {
            return countFinishedPVCs;
        }

        public ProofStatus getStatus() {
            return status;
        }

        @Override
        public String toString() {
            return "TreeNode{" +
                    "pvcCollection=" + pvcCollection +
                    ", type='" + type + '\'' +
                    ", name='" + name + '\'' +
                    ", countAllPVC=" + countAllPVC +
                    ", countFinishedPVCs=" + countFinishedPVCs +
                    ", status=" + status +
                    '}';
        }

        private ProofStatus status;


        private TreeNode(PVCCollection pvcCollection) {
            this.pvcCollection = pvcCollection;
            if (pvcCollection instanceof PVCGroup) {
                PVCGroup group = (PVCGroup) pvcCollection;
                DafnyDecl decl = group.getDafnyDecl();
                if (decl != null) {
                    type = getDeclType(decl);
                    name = " " + decl.getName();
                } else {
                    type = name = "";
                }
                this.countAllPVC = countPVCs(pvcCollection);
            } else

            if (pvcCollection instanceof SinglePVC) {
                SinglePVC singlePVC = (SinglePVC) pvcCollection;
                String fullName = singlePVC.getPVC().getIdentifier();
                String name = fullName.substring(fullName.indexOf('/')+1);
                this.name = name;
                this.type = "";
                this.countAllPVC = -1;
            } else {

                throw new Error("should not happen");
            }
        }

        public void updateTreeNode() {
            if (pvcCollection instanceof SinglePVC) {
                SinglePVC singlePVC = (SinglePVC) pvcCollection;
                String id = singlePVC.getPVC().getIdentifier();
                Proof proof = diveCenter.getProjectManager().getAllProofs().get(id);
                this.status = proof.getProofStatus();
            } else {
                boolean allGreen = true;
                boolean oneOrange = false;
                for (int i = 0; i < getChildCount(); i++) {
                    TreeNode c = (TreeNode) getChildAt(i);
                    c.updateTreeNode();
                    if (c.status != ProofStatus.CLOSED) {
                        allGreen = false;
                    }
                    if (c.status == ProofStatus.OPEN
                            || c.status == ProofStatus.FAILING) {
                        oneOrange = true;
                    }
                }
                if (allGreen) {
                    this.status = ProofStatus.CLOSED;
                } else if (oneOrange) {
                    this.status = ProofStatus.OPEN;
                } else {
                    this.status = ProofStatus.DIRTY;
                }

            }

        }

        public TreeNode findPVC(PVC pvc) {
            if (pvcCollection.isPVCLeaf() && pvcCollection.getPVC() == pvc) {
                return this;
            }
            if(children != null) {
                for (javax.swing.tree.TreeNode child : children) {
                    TreeNode pvcChild = (TreeNode) child;
                    TreeNode res = pvcChild.findPVC(pvc);
                    if (res != null) {
                        return res;
                    }
                }
            }

            return null;
        }
    }

    public PVCBrowserController(DiveCenter diveCenter) {
        this.diveCenter = diveCenter;
        Object[] noData = {};
        tree = new JTree(noData);
        tree.setCellRenderer(new PVCTreeRenderer(diveCenter));
        theComponent = new JScrollPane(tree);

        tree.addTreeSelectionListener(this::selectionChanged);
        tree.addMouseListener(doubleClickListener);
        diveCenter.properties().project.addObserver(this::updateProject);
        diveCenter.properties().activePVC.addObserver(this::updatePVC);
        diveCenter.properties().onGoingProof.addObserver(this::proofChanged);
        diveCenter.properties().noProjectMode.addObserver(
                b -> tree.setEnabled(!b));
    }

    private void proofChanged() {
        Object node = tree.getModel().getRoot();
        if (node instanceof TreeNode) {
            TreeNode root = (TreeNode) node;
            root.updateTreeNode();
        }
        tree.repaint();
    }

    private void selectionChanged(TreeSelectionEvent ev) {
        TreeNode leaf = (TreeNode) ev.getPath().getLastPathComponent();
        PVCCollection pvcCollection = leaf.pvcCollection;
        if (pvcCollection instanceof SinglePVC) {
            diveCenter.properties().activePVC.setValue(pvcCollection.getPVC());
        }
    }

    private void updateProject(Project project) {
        assert project != null;
        TreeNode root = makeTree(project.getAllPVCs());
        root.updateTreeNode();
        tree.setModel(new DefaultTreeModel(root));
    }

    private void updatePVC(PVC pvc) {
        if (pvc != null) {
            TreeNode root = (TreeNode) tree.getModel().getRoot();
            TreeNode pvcNode = root.findPVC(pvc);
            if (pvcNode != null) {
                tree.setSelectionPath(new TreePath(pvcNode.getPath()));
            }
        }
    }

    private TreeNode makeTree(PVCCollection node) {
        TreeNode result = new TreeNode(node);
        for (PVCCollection child : node.getChildren()) {
            result.add(makeTree(child));
        }
        return result;
    }

    public Component getComponent() {
        return theComponent;
    }

    private static String getDeclType(DafnyDecl decl) {
        DafnyTree rep = decl.getRepresentation();
        if (rep != null) {
            switch (rep.getType()) {
            case DafnyParser.METHOD:
                return "method";
            case DafnyParser.FUNCTION:
                return "function";
            case DafnyParser.CLASS:
                return "class";
            }
        }
        return "";
    }

    private static int countPVCs(PVCCollection coll) {
        List<PVCCollection> children = coll.getChildren();
        if (coll instanceof SinglePVC) {
            return 1;
        } else {
            return children.stream().mapToInt(PVCBrowserController::countPVCs).sum();
        }
    }
}
