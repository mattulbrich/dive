package edu.kit.iti.algover.project;

import edu.kit.iti.algover.parser.DafnyTree;

import java.io.File;
import java.util.List;

/**
 * Created by sarah on 8/5/16.
 */
public class DafnyCompilationUnit {
    /**
     * Path to directory of DafnyProject
     */
    private File dir;

    private List<DafnyLib> libraries;

    private List<DafnyDecl> dafnyDecls;

    private DafnyTree root;

    public DafnyCompilationUnit(DafnyCompilationUnit dcuBuilder){
        //call dafnydeclbuilder and feed list
    }

}
