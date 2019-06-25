package edu.kit.iti.algover.browser.callvisualization;

import edu.kit.iti.algover.dafnystructures.*;
import edu.kit.iti.algover.parser.DafnyTree;
import javafx.scene.Node;
import javafx.scene.layout.VBox;

import java.util.ArrayList;
import java.util.List;

/**
 * Entity of a call/callsite that is displayed in the list view (viewmodel)
 */
public class CallEntity {

    public CallEntity(){

    }

    public DafnyDecl getEntity() {
        switch(type){

            case METHOD:
                return method;
            case FUNCTION:
                return function;
            case FIELD:
                break;
            case CLASS:
                break;
        }
        return null;
    }

    public enum Type {
        METHOD, FUNCTION, FIELD, CLASS
    }

    /**
     * Type of the Callentity
     */
    private Type type;

    public Type getType() {
        return type;
    }

    /**
     * Tree
     */
    private DafnyTree callTree;

    private boolean call = false;

    public boolean getCall() {
        return call;
    }

    private boolean isHidden = true;

    private String headerText = "";



    /**
     * Fields of a Method
     */

    public DafnyMethod method;

    public List<DafnyTree> mPre;

    public List<DafnyTree> mPost;

    public List<DafnyTree> mArguments;

    public List<DafnyTree> mParams;

    /**
     * Fields of a Function
     */

    public DafnyFunction function;

    public List<DafnyTree> fPre;

    public List<DafnyTree> fPost;

    public List<DafnyTree> fArguments;

    public List<DafnyTree> fParams;


    public boolean isCall() {
        return call;
    }


    public boolean isHidden() {
        return isHidden;
    }

    public void setHidden(boolean hidden) {
        isHidden = hidden;
    }

    public String getHeaderText() {
        return headerText;
    }

    public int getUsageLine(){
        return this.callTree.getStartToken().getLine();
    }


    public Node getNode() {

        return new VBox();
    }
    public String getString(){
        switch (type){

            case METHOD:

                break;
            case FUNCTION:
                break;
            case FIELD:
                break;
            case CLASS:
                break;
        }
        return "";
    }
/*

    public VBox getDetailPane() {
        VBox vbox = new VBox();
        TextArea a = new TextArea();
        a.setEditable(false);
        List<String> l = new ArrayList<String>();
        //correspondingDecl.getRepresentation().accept(new DafnyTreeCallEntityVisitor(), l);
        vbox.getChildren().addAll(a);
        return vbox;
    }
*/

    public CallEntity(DafnyMethod m, DafnyTree t){


        this.type = Type.METHOD;
        this.method = m;
        if(t.getText().equals("CALL")){
            call = true;
        }
        this.mPre = m.getRequiresClauses();
        this.mParams = m.getParams();
        this.mPost = m.getEnsuresClauses();
        this.callTree = t;
        this.mArguments = callTree.getChildren().get(1).getChildren();



    }
    public CallEntity(DafnyFunction f, DafnyTree t){


        this.type = Type.FUNCTION;
        this.function = f;
        if(t.getText().equals("CALL")){
            call = true;
        }
        this.fPre = f.getRequiresClauses();
        this.fParams = f.getParameters();
        this.fPost = f.getEnsuresClauses();
        this.callTree = t;
        this.fArguments = callTree.getChildren().get(1).getChildren();

    }

    public String getEntityName(){
        switch(type){

            case METHOD:
                return method.getName();

            case FUNCTION:
                return function.getName();

            case FIELD:
                break;
            case CLASS:
                break;
        }
        return null;
    }




}
