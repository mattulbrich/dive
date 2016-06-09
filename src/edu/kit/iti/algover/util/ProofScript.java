package edu.kit.iti.algover.util;

import edu.kit.iti.algover.symbex.SymbexPath;

import java.util.LinkedList;

/**
 * Object which stores all applied rules to a proof obligation
 * If a split occurs it has to have pointers to children
 * Created by sarah on 9/17/15.
 */
public class ProofScript {
    LinkedList<RuleApp> appliedRules;
    SymbexPath po;
    public ProofScript (SymbexPath po){
        this.po = po;
        appliedRules = new LinkedList<RuleApp>();
    }
}
