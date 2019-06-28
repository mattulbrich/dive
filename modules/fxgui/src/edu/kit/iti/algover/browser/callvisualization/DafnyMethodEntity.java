package edu.kit.iti.algover.browser.callvisualization;

import edu.kit.iti.algover.dafnystructures.DafnyDecl;
import edu.kit.iti.algover.dafnystructures.DafnyMethod;
import edu.kit.iti.algover.parser.DafnyTree;
import javafx.scene.Node;
import javafx.scene.control.Label;
import javafx.scene.layout.VBox;

import java.util.List;

public class DafnyMethodEntity extends AbstractCallEntity {

    private Type type;

    private DafnyMethod method;

    private boolean isCall;

    private DafnyTree callTree;

    private boolean isHidden;

    private HighlightingHandler listener;
    /**
     * Fields of a Method
     */
    private List<DafnyTree> mPre;

    private List<DafnyTree> mPost;

    private List<DafnyTree> mArguments;

    private List<DafnyTree> mParams;


    public DafnyMethodEntity(DafnyMethod m, DafnyTree arg, HighlightingHandler listener) {
        this.listener = listener;
        this.type = Type.METHOD;
        this.method = m;
        if(arg.getText().equals("CALL")){
            isCall = true;
        }
        this.mPre = m.getRequiresClauses();
        this.mParams = m.getParams();
        this.mPost = m.getEnsuresClauses();
        this.callTree = arg;
        this.mArguments = callTree.getChildren().get(1).getChildren();
    }

    @Override
    public boolean isCall() {
        return this.isCall;
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
        return "Method "+method.getName();
    }

    @Override
    public int getUsageLine() {
        return callTree.getLine();
    }

    @Override
    public Node getNode() {
        VBox vbox= new VBox();
        Label name = new Label(getHeaderText()+ " (line "+getUsageLine()+")");
        name.setOnMouseClicked(event -> {
            listener.onRequestHighlight(callTree.getFilename(), method.getRepresentation().getToken(), callTree.getStopToken());
        });
        vbox.getChildren().add(name);
        vbox.getChildren().addAll(createArguments());
        if(mPre != null && mPre.size() > 0){
            vbox.getChildren().addAll(createPre());
        }

        return vbox;
    }

    private Node createArguments() {
        Label name = new Label("Arguments: ");
        name.setOnMouseClicked(event -> {
            mArguments.size();
            mParams.size();
        });
        mArguments.size();
        return name;
    }

    private Node[] createPre() {
        return null;
    }

    @Override
    public Type getType() {
        return this.type;
    }

    @Override
    public String getString() {
        return getHeaderText();
    }

    @Override
    public String getEntityName() {
        return method.getName();
    }

    @Override
    public DafnyDecl getEntity() {
        return this.method;
    }
}
