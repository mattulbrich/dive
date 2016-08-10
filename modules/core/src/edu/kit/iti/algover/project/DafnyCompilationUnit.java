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

    /**
     * List of libararies imported in this compilationunit
     */
    private List<DafnyLib> libraries;

    /**
     * List of all dafnydecls, can be DafnyClass, DafnyFunction, DafnyField
     */
    private List<DafnyDecl> dafnyDecls;

    /**
     * reference to root of DafnyTree
     */
    private DafnyTree root;

    public DafnyCompilationUnit(DafnyCompilationUnit dcuBuilder){
        //call dafnydeclbuilder and feed list
        //traverse root, get dafny untertrees
        //call dafnydeclbuilder with tree

    }

}
