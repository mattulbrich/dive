package edu.kit.iti.algover.project;

import edu.kit.iti.algover.parser.DafnyParser;
import edu.kit.iti.algover.parser.DafnyTree;

import java.util.List;
import java.util.ListIterator;

/**
 * Created by sarah on 8/4/16.
 */
public class DafnyFunction extends DafnyDecl{

    private List<DafnyTree> parameters;
    private DafnyTree returnType;
    private String name;
    private DafnyTree body;

    public DafnyFunction (DafnyTree function){
        //this.name = function.getChild(0).getText();
        int childCount = function.getChildCount();
        traverseTree(function, childCount);
//        this.parameters = function.getChildrenWithType(DafnyParser.ARGS);
        //this.returnType = ;


    }
    public void traverseTree(DafnyTree function, int count){
        this.name = function.getChild(0).getText();
        DafnyTree child;
        for(int i = 1; i < count; i++){
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
                default:
                    this.body = child;
                    break;
            }
        }

    }

    //TODO
    public String toString(){
        String s = "function "+this.name;
        String params = "";
        if(this.parameters != null){
            for (DafnyTree para:this.parameters) {
                params+=para.toStringTree();
            }
        }else{
            params ="()";
        }
        s+=params;

        return s;
    }

}
