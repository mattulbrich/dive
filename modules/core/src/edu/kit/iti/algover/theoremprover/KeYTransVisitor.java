package edu.kit.iti.algover.theoremprover;

import edu.kit.iti.algover.term.DefaultTermVisitor;
import edu.kit.iti.algover.term.Term;

/**
 * Created by sarah on 9/23/16.
 */
public class KeYTransVisitor extends DefaultTermVisitor<Void, String> {
    @Override
    protected String defaultVisit(Term term, Void arg) {
        return null;
    }
}