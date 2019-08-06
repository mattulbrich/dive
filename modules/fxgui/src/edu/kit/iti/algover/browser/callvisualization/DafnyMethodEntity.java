package edu.kit.iti.algover.browser.callvisualization;

import edu.kit.iti.algover.dafnystructures.DafnyDecl;
import edu.kit.iti.algover.dafnystructures.DafnyMethod;
import edu.kit.iti.algover.parser.DafnyTree;
import javafx.geometry.Pos;
import javafx.scene.Node;
import javafx.scene.control.Label;
import javafx.scene.control.TitledPane;
import javafx.scene.input.MouseEvent;
import javafx.scene.layout.HBox;
import javafx.scene.layout.Priority;
import javafx.scene.layout.Region;
import javafx.scene.layout.VBox;

import java.util.List;

/**
 * Representation of a DafnyMethod in the call tree for the GUI
 * The method getNode() returns the View of this component
 */
public class DafnyMethodEntity extends AbstractCallEntity {

    private Type type;

    private DafnyMethod method;

    private boolean isCall;

    private DafnyTree callTree;

    private boolean isHidden = false;

    private HighlightingHandler listener;
    /**
     * Fields of a Method
     */
    private List<DafnyTree> mPre;

    private List<DafnyTree> mPost;

    private List<DafnyTree> mArguments;

    private List<DafnyTree> mParams;

    private DafnyTree mDecreasesClause;

    private List<ParamValueObject> paramArgsList;

    public DafnyMethodEntity(DafnyMethod m, DafnyTree arg, HighlightingHandler listener, boolean isCall) {
        this.listener = listener;
        this.type = Type.METHOD;
        this.method = m;
        this.isCall = isCall;
        this.mPre = m.getRequiresClauses();
        this.mParams = m.getParams();
        this.mPost = m.getEnsuresClauses();
        this.callTree = arg;
        this.mArguments = callTree.getChildren().get(1).getChildren();
        this.mDecreasesClause = m.getDecreasesClause();

        paramArgsList = extractParams(mArguments, mParams);
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
        if(!isCall()){
            return getOuterEntity(callTree);
        } else {
            return "Method " + method.getName();
        }
    }



    @Override
    public int getUsageLine() {
        return callTree.getLine();
    }

    @Override
    public Node getNode() {
        TitledPane tp = new TitledPane();
        VBox vbox= new VBox();
        vbox.setBackground(WHITE_BACKGROUND);
        vbox.setSpacing(10);

        AnimatedLabel name = new AnimatedLabel(getHeaderText(), callTree, listener);
        name.setAlignment(Pos.BOTTOM_LEFT);
        AnimatedLabel lineNumber = new AnimatedLabel("(line "+getUsageLine()+")", callTree, listener);
        lineNumber.setAlignment(Pos.CENTER_RIGHT);

        HBox nameBox = new HBox();
        nameBox.getChildren().add(name);
        Region spacer = new Region();
        HBox.setHgrow(spacer, Priority.ALWAYS);
        nameBox.getChildren().add(spacer);
        nameBox.getChildren().add(lineNumber);


        vbox.getChildren().add(nameBox);
        if(!paramArgsList.isEmpty()) {
            vbox.getChildren().add(createArgumentView(paramArgsList, listener));
        } else {
            vbox.getChildren().add(new Label("This method has no parameters"));
        }
        if(mPre.size() > 0) {
            vbox.getChildren().add(createPreconditionView(mPre, listener));
        }
        if(mPost.size() > 0){
            vbox.getChildren().add(createPostconditionView(mPost, listener));
        }

        if(mDecreasesClause != null){
            vbox.getChildren().add(createDecreasesView(mDecreasesClause, listener));
        }

        tp.setText(getHeaderText()+" @line "+getUsageLine());
        tp.setContent(vbox);
        tp.setCollapsible(true);
        tp.setExpanded(false);
        AnimatedLabelMouseEventHandler eventHandler = new AnimatedLabelMouseEventHandler(name, callTree, listener);
        tp.addEventHandler(MouseEvent.MOUSE_ENTERED, eventHandler);
        tp.addEventHandler(MouseEvent.MOUSE_EXITED, eventHandler);

        return tp;
    //    return vbox;

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
