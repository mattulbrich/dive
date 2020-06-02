/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 *
 */

package edu.kit.iti.algover.swing.sequent;

import edu.kit.iti.algover.dafnystructures.DafnyClass;
import edu.kit.iti.algover.dafnystructures.DafnyDecl;
import edu.kit.iti.algover.project.Project;
import edu.kit.iti.algover.proof.PVC;
import edu.kit.iti.algover.proof.PVCCollection;
import edu.kit.iti.algover.swing.DiveCenter;
import edu.kit.iti.algover.swing.actions.BarAction;
import edu.kit.iti.algover.swing.actions.BarManager.Initialisable;
import edu.kit.iti.algover.swing.util.Underline;

import javax.swing.*;
import javax.swing.border.EtchedBorder;
import java.awt.*;
import java.awt.event.MouseAdapter;
import java.awt.event.MouseEvent;
import java.util.ArrayList;
import java.util.List;

import static java.awt.Color.BLUE;

public class Breadcrumbs extends JPanel implements Initialisable {

    private static final Font LABEL_FONT = new Font("sans-serif", Font.PLAIN, 12);
    private DiveCenter center;
    private final JLabel classLabel;
    private final JLabel methLabel;
    private final JLabel pvcLabel;

    private class BlueListener extends MouseAdapter {
        private JLabel label;

        private BlueListener(JLabel label) {
            this.label = label;
        }

        @Override
        public void mouseEntered(MouseEvent e) {
            label.setBorder(new Underline(BLUE));
        }

        @Override
        public void mouseExited(MouseEvent e) {
            label.setBorder(BorderFactory.createEmptyBorder());
        }

        @Override
        public void mouseClicked(MouseEvent e) {
            if (SwingUtilities.isLeftMouseButton(e) && e.getClickCount() == 1) {
                showDropDownList(label);
            }
        }
    }

    public Breadcrumbs() {
        setLayout(new FlowLayout(FlowLayout.LEFT));
        {
            this.classLabel = new JLabel();
            classLabel.setFont(LABEL_FONT);
            classLabel.addMouseListener(new BlueListener(classLabel));
            add(classLabel);
        }
        add(new JLabel(">"));
        {
            this.methLabel = new JLabel();
            methLabel.setFont(LABEL_FONT);
            methLabel.addMouseListener(new BlueListener(methLabel));
            add(methLabel);
        }
        add(new JLabel(">"));
        {
            this.pvcLabel = new JLabel();
            pvcLabel.setFont(LABEL_FONT);
            pvcLabel.addMouseListener(new BlueListener(pvcLabel));
            add(pvcLabel);
        }

        // setPreferredSize(new Dimension(300,0));
        setBorder(BorderFactory.createEtchedBorder(EtchedBorder.LOWERED));
        setMaximumSize(new Dimension(500,30));
    }

    public void initialised() {
        this.center = (DiveCenter) getClientProperty(BarAction.CENTER);
        center.properties().activePVC.addObserver(this::updatePVC);
        center.properties().noProjectMode.addObserver(this::updatePVC);
    }

    private void updatePVC() {

        Boolean noProjMode = center.properties().noProjectMode.getValue();
        PVC pvc = center.properties().activePVC.getValue();
        if (noProjMode || pvc == null) {
            if (noProjMode) {
                classLabel.setText("No project");
            } else {
                classLabel.setText("No proof obligation chosen");
            }
            classLabel.setEnabled(false);
            methLabel.setText("");
            pvcLabel.setText("");
            return;
        }

        classLabel.setEnabled(true);
        String id = pvc.getIdentifier();
        int slash = id.indexOf('/');
        String classMeth = id.substring(0, slash);
        int dot = classMeth.indexOf('.');
        if (dot > 0) {
            String clss = classMeth.substring(0, dot);
            classLabel.setText(clss);
        } else {
            classLabel.setText("<html><i>No class</i>");
        }
        String meth = classMeth.substring(dot + 1);
        methLabel.setText(meth);

        pvcLabel.setText(id.substring(slash + 1));
    }

    private void showDropDownList(JLabel label) {

        if(center.properties().noProjectMode.getValue()) {
            // no selection if in edit mode.
            return;
        }

        JPopupMenu popup = new JPopupMenu();
        if(label == classLabel) {
            classMenu(popup);
        } else if (label == methLabel) {
            PVC current = center.properties().activePVC.getValue();
            if (current == null) {
                return;
            }
            DafnyDecl p = current.getDeclaration().getParentDecl();
            if (p instanceof DafnyClass) {
                methodMenu((DafnyClass)p, popup);
            }
        }  else if (label == pvcLabel) {
            PVC current = center.properties().activePVC.getValue();
            if (current == null) {
                return;
            }
            DafnyDecl d = current.getDeclaration();
            pvcMenu(d, popup);
        }

        popup.show(label, 0, label.getHeight());
    }

    private void classMenu(JComponent menu) {
        Project project = center.properties().project.getValue();

        JMenu item = new JMenu("<html><i>No class</i>");
        menu.add(item);
        methodMenu(null, item);
        if (item.getMenuComponentCount() == 0) {
            item.setEnabled(false);
        }

        for (DafnyClass clss : project.getClasses()) {
            item = new JMenu(clss.getName());
            menu.add(item);
            methodMenu(clss, item);
            if (item.getMenuComponentCount() == 0) {
                item.setEnabled(false);
            }
        }
    }

    private void methodMenu(DafnyClass clss, JComponent menu) {
        List<DafnyDecl> decls = new ArrayList<>();
        if(clss != null) {
            decls.addAll(clss.getFunctions());
            decls.addAll(clss.getMethods());
        } else {
            Project project = center.properties().project.getValue();
            decls.addAll(project.getFunctions());
            decls.addAll(project.getMethods());
        }

        for (DafnyDecl decl : decls) {
            JMenu item = new JMenu(decl.getName());
            menu.add(item);
            pvcMenu(decl, item);
            if (item.getMenuComponentCount() == 0) {
                item.setEnabled(false);
            }
        }
    }

    private void pvcMenu(DafnyDecl decl, JComponent menu) {
        Project project = center.properties().project.getValue();
        PVCCollection pvcs = project.getPVCsFor(decl);

        for (PVCCollection node : pvcs.getChildren()) {
            PVC pvc = node.getPVC();
            String id = pvc.getIdentifier();
            JMenuItem item = new JMenuItem(id.substring(id.indexOf('/') + 1));
            item.addActionListener(e -> center.properties().activePVC.setValue(pvc));
            menu.add(item);
        }
    }


}
