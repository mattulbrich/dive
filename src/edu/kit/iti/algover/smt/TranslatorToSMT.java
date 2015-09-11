package edu.kit.iti.algover.smt;

import edu.kit.iti.algover.parser.DafnyTree;

/**
 * Created by sarah on 8/13/15.
 */
public class TranslatorToSMT {

    public static String INT_SORT = "Int";
    public static String ALL = "forall";
    public static String EXISTS = "exists";
    DafnyTree tree;
    public TranslatorToSMT(DafnyTree t){
        this.tree=t;
    }

    public String createSMTInput(){
        return null;

    }

}
