/*
 * This file is part of DIVE.
 *
 * DIVE is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * Foobar is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with Foobar.  If not, see <https://www.gnu.org/licenses/>.
 */

package edu.kit.iti.algover.rule.script;

import edu.kit.iti.algover.PropertyManager;
import javafx.scene.web.WebEngine;
import javafx.scene.web.WebView;

public class BlocklyController {
    private final WebView view;
    private final WebEngine engine;

    public BlocklyController() {
        view = new WebView();
        engine = view.getEngine();

        PropertyManager.getInstance().currentProof.addListener(((observable, oldValue, newValue) -> {
            if(newValue != null) {
                String content = ProofHTML.toHTML(newValue.getProofScript());
                engine.loadContent(content);
            }
        }));
    }

    public WebView getView() {
        return view;
    }

    public void insertTextForSelectedNode(String s) {
    }
}
