package edu.kit.iti.algover.project;

import edu.kit.iti.algover.parser.DafnyTree;
import edu.kit.iti.algover.term.Sort;
import edu.kit.iti.algover.util.Pair;

import java.util.List;

/**
 * Created by sarah on 8/4/16.
 */
public class DafnyMethod extends DafnyDecl {

    private String methodName;
    private List<Pair<Sort, String>> params;
    private List<Pair<Sort, String>> returns;


    private Precondition pre;
    private Postcondition post;

    private MethodBody body;

    public DafnyMethod(DafnyTree method){
        //TODO
    }

}
