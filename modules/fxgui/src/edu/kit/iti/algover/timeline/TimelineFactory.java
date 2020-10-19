package edu.kit.iti.algover.timeline;

import edu.kit.iti.algover.browser.BrowserController;
import edu.kit.iti.algover.editor.EditorController;
import edu.kit.iti.algover.rule.RuleApplicationController;
import edu.kit.iti.algover.rule.script.ScriptView;
import edu.kit.iti.algover.sequent.SequentTabViewController;

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
                                                              RuleApplicationController ruleApplicationController,
                                                              ScriptView scriptView) {
        TimelineLayout tll = new TimelineLayout(browserController.getView(), editorController.getView(),
                sequentTabViewController.getView(), ruleApplicationController.getView(), scriptView);

        tll.setDividerPosition(0.5);

        return tll;
    }


}
