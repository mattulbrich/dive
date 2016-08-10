package edu.kit.iti.algover.project;

import edu.kit.iti.algover.parser.DafnyParser;
import edu.kit.iti.algover.parser.DafnyTree;

import java.util.LinkedList;
import java.util.List;
import java.util.ListIterator;

/**
 * Class representing a single Dafnyfunction
 */
public class DafnyFunction extends DafnyDecl{
    /**
     * The parameters of teh function, possibly empty
     */
    private List<DafnyTree> parameters;

    /**
     * The return type of teh function. Non-null
     */
    private DafnyTree returnType;

    /**
     * The name of the function
     */
    private String name;

    /**
     * The function's body. Only one single line allowed
     */
    private DafnyTree body;


    /**
     * Constructor for DafnyFunction
     * @param function
     *          DafnyTree  with DafnyParser.FUNCTION as root
     */
    public DafnyFunction (DafnyTree function){
        int childCount = function.getChildCount();
        this.parameters = new LinkedList<>();
        traverseTree(function, childCount);
    }

    public void traverseTree(DafnyTree function, int count){
        this.name = function.getChild(0).getText();

        DafnyTree child;
        int i = 1;
        for(; function.getChild(i).getType() == DafnyParser.VAR && i < count; i++){
            this.parameters.add(function.getChild(i));
        }

        this.returnType = function.getChild(i);

        for(int z = 1; z < count; z++){
            child = function.getChild(i);
            switch(child.getType()){
                case DafnyParser.VAR:
                    this.parameters.add(child);
                    break;
                case DafnyParser.INT:
                    this.returnType = child;
                    break;
                case DafnyParser.BOOL:
                    this.returnType = child;
                    break;
                case DafnyParser.SET:
                    this.returnType = child;
                    break;
                //TODO restliche Typen
                default:
                    this.body = child;
                    break;
            }
        }

    }

    /**
     * ToString Method
     * TODO Returntype and body
     * @return
     */
    public String toString(){
        String s = "function "+this.name;

        if(this.parameters != null){
            String params = "(";

            for (DafnyTree para:this.parameters) {
                params+=para.toStringTree();
            }


            s+=params+")";
        }


        return s;
    }

}
