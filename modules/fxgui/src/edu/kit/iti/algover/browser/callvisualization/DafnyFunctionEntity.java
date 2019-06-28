package edu.kit.iti.algover.browser.callvisualization;

import edu.kit.iti.algover.dafnystructures.DafnyDecl;
import edu.kit.iti.algover.dafnystructures.DafnyFunction;
import edu.kit.iti.algover.parser.DafnyTree;
import javafx.scene.Node;
import javafx.scene.control.Label;
import javafx.scene.layout.VBox;

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

    private HighlightingHandler listener;

    /**
     * Fields of a Function
     */

    public DafnyFunction function;

    private List<DafnyTree> fPre;

    private List<DafnyTree> fPost;

    private List<DafnyTree> fArguments;

    private List<DafnyTree> fParams;

    public DafnyFunctionEntity(DafnyFunction f, DafnyTree t, HighlightingHandler listener){

        this.listener = listener;

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
        this.headerText = "Function "+f.getName();

    }

    @Override
    public DafnyDecl getEntity() {
        return this.function;
    }

    @Override
    public boolean isCall() {
        return this.call;
    }

    @Override
    public boolean isHidden() {
        return this.isHidden;
    }

    @Override
    public void setHidden(boolean hidden) {
        this.isHidden = hidden;
    }

    @Override
    public String getHeaderText() {
        return this.headerText;
    }

    @Override
    public int getUsageLine() {
        return callTree.getLine();
    }

    @Override
    public Node getNode() {
        VBox vbox= new VBox();
        Label name = new Label(headerText + " (line" + getUsageLine()+")");
        name.setOnMouseClicked(event -> {
            listener.onRequestHighlight(callTree.getFilename(), callTree.getStartToken(), callTree.getStopToken());
        });
        vbox.getChildren().add(name);
        vbox.getChildren().add(createArguments());

        return vbox;


    }

    private Node createArguments() {
        Label name = new Label("Arguments: ");
        name.setOnMouseClicked(event -> {
            fArguments.size();
            fParams.size();
        });
        fArguments.size();
        return name;
    }

    @Override
    public String getString() {
        return this.headerText;
    }



    @Override
    public String getEntityName() {
        return this.getEntity().getName();
    }
}
