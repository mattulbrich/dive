/*
  DIVE
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
package edu.kit.iti.algover.swing.actions;

import java.awt.event.ActionEvent;

import edu.kit.iti.algover.swing.help.ReferenceManualWindow;
import edu.kit.iti.algover.swing.util.ExceptionDialog;

/**
 * This action launches the reference manual window.
 * It does not create a fresh instance every time.
 * 
 * @author mattias ulbrich
 */

@SuppressWarnings("serial")
public class ReferenceManualAction extends BarAction {

    private ReferenceManualWindow window;

    @Override
    public void actionPerformed(ActionEvent e) {
        
        try {
            if(window == null) {
                window = new ReferenceManualWindow();
            }
        } catch (Exception ex) {
            ExceptionDialog.showExceptionDialog(getParentFrame(), ex);
        }

        window.setLocationRelativeTo(getParentFrame());
        window.setVisible(true);
    }
}
