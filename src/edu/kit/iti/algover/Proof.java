package edu.kit.iti.algover;

import edu.kit.iti.algover.symbex.PathConditionElement;
import edu.kit.iti.algover.symbex.SymbexState;

import java.io.File;
import java.util.LinkedList;

/**
 * Class that represents a proof with all its components and references
 * A proof object consists of a problem file, and a proof obligation (contained in a symbex state)
 *
 *
 */
public class Proof {

    public File problemFile;
    public SymbexState proofObligation;



    public Proof(File problemFile, SymbexState pO){
        this.problemFile = problemFile;
        this.proofObligation = pO;


    }


}
