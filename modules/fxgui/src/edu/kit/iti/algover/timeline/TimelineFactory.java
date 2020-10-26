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

package edu.kit.iti.algover.timeline;

import edu.kit.iti.algover.browser.BrowserController;
import edu.kit.iti.algover.editor.EditorController;
import edu.kit.iti.algover.rule.RuleApplicationController;
import edu.kit.iti.algover.rule.script.ScriptCodeView;
import edu.kit.iti.algover.sequent.SequentTabViewController;

/**
 * This class dscribes a (static) Factory for TimelineLayout. It
 * implements static methods to create and return TimelineLayouts
 * @author Valentin Springsklee
 */
public class TimelineFactory {

    public enum DefaultViewPosition {

        BROWSER_EDITOR(0),
        EDITOR_SEQUENT(1),
        SEQUENT_RULE(2);

        public final int index;

        DefaultViewPosition (int index) {
            this.index = index;
        }
    }

    /**
     * Create a TimelineLayout with the default GUI components for the DIVE Application.
     *
     * Browser - Dafny editor - sequent - rule script and application
     *
     * @param browser
     * @param dafnyEditor
     * @param sequent
     * @param ruleApplicator
     * @return The "default" timeline layout for DIVE
     */
    public static TimelineLayout getDefaultTimeLineLayout(BrowserController browser,
                                                   EditorController dafnyEditor,
                                                   SequentTabViewController sequent,
                                                   RuleApplicationController ruleApplicator) {
        TimelineLayout tll = new TimelineLayout(browser.getView(),
                dafnyEditor.getView(),
                sequent.getView(),
                ruleApplicator.getView());

        tll.setDividerPosition(0.2);

        return tll;
    }

    public static TimelineLayout testWebviewAlongScriptEditor(BrowserController browserController,
                                                              EditorController editorController,
                                                              SequentTabViewController sequentTabViewController,
                                                              RuleApplicationController ruleApplicationController) {
        TimelineLayout tll = new TimelineLayout(browserController.getView(), editorController.getView(),
                sequentTabViewController.getView(), ruleApplicationController.getView(),
                ruleApplicationController.getScriptView());

        tll.setDividerPosition(0.5);

        return tll;
    }


}
