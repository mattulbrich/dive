package edu.kit.iti.algover.rule;

import java.util.Comparator;

public class RuleGridComparator {

    public static Comparator<RuleView> compareAlphaOrder = new Comparator<RuleView>() {
        @Override
        public int compare(RuleView o1, RuleView o2) {
            int caseInsensitiveOrder = String.CASE_INSENSITIVE_ORDER.compare(o1.getRule().getName(), o2.getRule().getName());
            if (caseInsensitiveOrder == 0) {
                caseInsensitiveOrder = o1.getRule().getName().compareTo(o2.getRule().getName());
            }
            return caseInsensitiveOrder;
        }
    };

    public static Comparator<RuleView> compareBranching = new Comparator<RuleView>() {
        @Override
        public int compare(RuleView o1, RuleView o2) {
            int caseInsensitiveOrder = Integer.compare(o1.getApplication().getBranchInfo().size(), o2.getApplication().getBranchInfo().size());
            if (caseInsensitiveOrder == 0) {
                caseInsensitiveOrder = o1.getRule().getName().compareTo(o2.getRule().getName());
            }
            return caseInsensitiveOrder;
        }
    };
}
