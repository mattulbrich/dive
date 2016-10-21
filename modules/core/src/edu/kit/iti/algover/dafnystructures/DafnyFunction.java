package edu.kit.iti.algover.dafnystructures;

import edu.kit.iti.algover.parser.DafnyTree;

import java.io.File;
import java.util.List;

/**
 * Class representing a single Dafnyfunction
 * A function has zero or n arguments, a return type, zero or more contracts and a body
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

    public List<DafnyTree> getParameters() {
        return parameters;
    }

    public DafnyTree getReturnType() {
        return returnType;
    }

    @Override
    public String getName() {
        return name;
    }

    public DafnyTree getBody() {
        return body;
    }

    public List<DafnyTree> getPres() {
        return pres;
    }

    public List<DafnyTree> getPosts() {
        return posts;
    }

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
     * @param filename
     * @param t
     * @param name
     * @param params
     * @param returnType
     * @param body
     * @param pres
     * @param posts
     */
    public DafnyFunction(File file, DafnyTree t,
                         String name,
                         List<DafnyTree> params,
                         DafnyTree returnType,
                         DafnyTree body,
                         List<DafnyTree> pres,
                         List<DafnyTree> posts){
        super(file, t, name);
        this.name = name;
        this.parameters = params;
        this.returnType = returnType;
        this.body = body;
        this.pres = pres;
        this.posts = posts;

    }


//    public void traverseTree(DafnyTree function, int count){
//        this.name = function.getChild(0).getText();
//
//        this.parameters = function.getChildrenWithType(DafnyParser.ARGS);
//        //this.posts = function.getChildrenWithType(DafnyParser.ENSURES);
//        //this.pres= function.getChildrenWithType(DafnyParser.REQUIRES);
//        //this.body= function.getChildrenWithType(DafnyParser.BLOCK);
//        //this.returnType = function.getChildrenWithType(DafnyParser.RETURNS);
//
//       /*// DafnyTree child;
//        int i = 1;
//        for(; function.getChild(i).getType() == DafnyParser.ARGS && i < count; i++){
//            this.parameters.addAll(function.getChild(i).getChildrenWithType(DafnyParser.VAR));
//
//        }
//
//        this.returnType = function.getChild(i).getChild(0);
//        i++;
//        if((function.getChild(i).getType() == DafnyParser.ENSURES) ||
//        (function.getChild(i).getType() == DafnyParser.REQUIRES)){
//            for(; function.getChild(i).getType() == DafnyParser.REQUIRES && i < count; i++){
//                this.pres.add(function.getChild(i));
//            }
//            for(; function.getChild(i).getType() == DafnyParser.ENSURES && i < count; i++){
//                this.posts.add(function.getChild(i));
//            }
//        }
//        if(function.getChild(i).getType() == DafnyParser.BLOCK) {
//            this.body =function.getChild(i).getChild(0);
//        }*/
//
//
//
//    }


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
    @Override
    public <R, A> R accept(DafnyDeclVisitor<R,A> visitor, A arg) {
        return visitor.visit(this, arg);
    }
}
