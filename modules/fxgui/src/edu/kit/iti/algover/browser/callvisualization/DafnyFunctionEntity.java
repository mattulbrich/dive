package edu.kit.iti.algover.browser.callvisualization;

import edu.kit.iti.algover.dafnystructures.DafnyDecl;
import edu.kit.iti.algover.dafnystructures.DafnyFunction;
import edu.kit.iti.algover.parser.DafnyTree;
import javafx.scene.Node;

import java.util.List;

public class DafnyFunctionEntity extends AbstractCallEntity {

    /**
     * Type of the Callentity
     */
    private Type type;

    @Override
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
     * Fields of a Function
     */

    public DafnyFunction function;

    public List<DafnyTree> fPre;

    public List<DafnyTree> fPost;

    public List<DafnyTree> fArguments;

    public List<DafnyTree> fParams;

    public DafnyFunctionEntity(DafnyFunction f, DafnyTree t){


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

    @Override
    public DafnyDecl getEntity() {
        return this.getEntity();
    }

    @Override
    public boolean isCall() {
        return this.isCall();
    }

    @Override
    public boolean isHidden() {
        return this.isHidden();
    }

    @Override
    public void setHidden(boolean hidden) {
        this.isHidden = hidden;
    }

    @Override
    public String getHeaderText() {
        return this.getHeaderText();
    }

    @Override
    public int getUsageLine() {
        return this.getUsageLine();
    }

    @Override
    public Node getNode() {
        return this.getNode();
    }

    @Override
    public String getString() {
        return this.getString();
    }



    @Override
    public String getEntityName() {
        return this.getEntityName();
    }
}
