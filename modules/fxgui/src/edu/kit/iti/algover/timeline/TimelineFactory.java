package edu.kit.iti.algover.timeline;

import edu.kit.iti.algover.browser.BrowserController;
import edu.kit.iti.algover.editor.EditorController;
import edu.kit.iti.algover.rule.RuleApplicationController;
import edu.kit.iti.algover.sequent.SequentTabViewController;

public class TimelineFactory {

    public static final int BROWSER_EDITOR  = 0;
    public static final int EDITOR_SEQUENT  = 1;
    public static final int SEQUENT_RULE    = 2;

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

}
