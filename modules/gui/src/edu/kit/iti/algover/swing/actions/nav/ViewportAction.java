/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 *
 */

package edu.kit.iti.algover.swing.actions.nav;

import edu.kit.iti.algover.swing.Viewport;
import edu.kit.iti.algover.swing.actions.BarAction;
import edu.kit.iti.algover.swing.actions.BarManager.InitialisingAction;

import java.awt.event.ActionEvent;

public class ViewportAction {

    public static class Left extends BarAction implements InitialisingAction {
        @Override
        public void initialised() {
            getDiveCenter().properties().viewPort.addObserver(vp -> setEnabled(vp != Viewport.PVC_VIEW));
        }

        @Override
        public void actionPerformed(ActionEvent actionEvent) {
            getDiveCenter().moveViewport(-1);
        }
    }

    public static class Right extends BarAction implements InitialisingAction {
        @Override
        public void initialised() {
            getDiveCenter().properties().viewPort.addObserver(vp -> setEnabled(vp != Viewport.PROOF_VIEW));
        }

        @Override
        public void actionPerformed(ActionEvent actionEvent) {
            getDiveCenter().moveViewport(+1);
        }
    }

    public static class PVC extends BarAction {
        @Override
        public void actionPerformed(ActionEvent actionEvent) {
            getDiveCenter().properties().viewPort.setValue(Viewport.PVC_VIEW);
        }
    }

    public static class Code extends BarAction {
        @Override
        public void actionPerformed(ActionEvent actionEvent) {
            getDiveCenter().properties().viewPort.setValue(Viewport.CODE_VIEW);
        }
    }

    public static class Proof extends BarAction {
        @Override
        public void actionPerformed(ActionEvent actionEvent) {
            getDiveCenter().properties().viewPort.setValue(Viewport.PROOF_VIEW);
        }
    }
}
