/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.rules;

import edu.kit.iti.algover.term.Term;

import java.util.List;

/**
 * Created by sarah on 10/7/15.
 */
public class ProofStep {

    private List<Term> addList;
    private List<Term> delList;
    public int countBranches() {
        // TODO Auto-generated method stub
        return 0;
    }
    public static ProofStep closeStep() {
        return new ProofStep();
    }


}
