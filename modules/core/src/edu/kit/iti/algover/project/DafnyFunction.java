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
     * The parameters of the function, possibly empty
     */
    private List<DafnyTree> parameters;

    /**
     * The return type of the function. Non-null
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


    private List<DafnyTree> pres;
    private List<DafnyTree> posts;

    /**
     * Constructor for DafnyFunction
     * @param function
     *          DafnyTree  with DafnyParser.FUNCTION as root
     */
    public DafnyFunction (DafnyTree function){
        int childCount = function.getChildCount();
        this.parameters = new LinkedList<>();
        this.pres = new LinkedList<>();
        this.posts= new LinkedList<>();
        traverseTree(function, childCount);
    }

    public void traverseTree(DafnyTree function, int count){
        this.name = function.getChild(0).getText();

        this.parameters = function.getChildrenWithType(DafnyParser.ARGS);
        this.posts = function.getChildrenWithType(DafnyParser.ENSURES);
        this.pres= function.getChildrenWithType(DafnyParser.REQUIRES);
        //this.body= function.getChildrenWithType(DafnyParser.BLOCK);
        //this.returnType = function.getChildrenWithType(DafnyParser.RETURNS);

       /*// DafnyTree child;
        int i = 1;
        for(; function.getChild(i).getType() == DafnyParser.ARGS && i < count; i++){
            this.parameters.addAll(function.getChild(i).getChildrenWithType(DafnyParser.VAR));

        }

        this.returnType = function.getChild(i).getChild(0);
        i++;
        if((function.getChild(i).getType() == DafnyParser.ENSURES) ||
        (function.getChild(i).getType() == DafnyParser.REQUIRES)){
            for(; function.getChild(i).getType() == DafnyParser.REQUIRES && i < count; i++){
                this.pres.add(function.getChild(i));
            }
            for(; function.getChild(i).getType() == DafnyParser.ENSURES && i < count; i++){
                this.posts.add(function.getChild(i));
            }
        }
        if(function.getChild(i).getType() == DafnyParser.BLOCK) {
            this.body =function.getChild(i).getChild(0);
        }*/



    }


    /**
     * ToString Method
     * @return
     */
    public String toString(){
        String s = "function "+this.name+"\n";

        if(this.parameters != null){
            String params = this.parameters.size()+" Parameters: ";

            for (DafnyTree para:this.parameters) {
                params+=para.toStringTree()+"\n";
            }
            s+=params+"\n";
        }
//        s += "returns "+this.returnType.toStringTree()+"\n";
//        s += "with body \n"+this.body.toStringTree();

        return s;
    }

}
