package edu.kit.iti.algover.project;

import edu.kit.iti.algover.parser.DafnyParser;
import edu.kit.iti.algover.parser.DafnyTree;

/**
 * I guess this class will be obsolete
 * Created by sarah on 8/8/16.
 */
public class DafnyDeclBuilder {

    private DafnyTree tree;

    public DafnyDeclBuilder(DafnyTree toBuild){
        switch(toBuild.getType()){
            case DafnyParser.FUNCTION:
                buildFunction(toBuild);
                break;
            case DafnyParser.METHOD:
                buildMethod(toBuild);
                break;
            case DafnyParser.CLASS:
                buildClass(toBuild);
                break;
            default:
                buildField(toBuild);
                break;
        }
    }

    private void buildMethod(DafnyTree toBuild) {
        System.out.println("Building Method");
    }

    private void buildClass(DafnyTree toBuild) {
        System.out.println("Building Class");
    }

    private void buildField(DafnyTree toBuild) {
        System.out.println("Building Field");
    }

    private void buildFunction(DafnyTree toBuild) {
        System.out.println("Building Function");
    }


}
