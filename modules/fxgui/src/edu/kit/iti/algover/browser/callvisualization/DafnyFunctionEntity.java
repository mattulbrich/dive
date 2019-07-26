package edu.kit.iti.algover.browser.callvisualization;

import edu.kit.iti.algover.dafnystructures.DafnyDecl;
import edu.kit.iti.algover.dafnystructures.DafnyFunction;
import edu.kit.iti.algover.parser.DafnyParser;
import edu.kit.iti.algover.parser.DafnyTree;
import javafx.scene.Node;
import javafx.scene.control.Label;
import javafx.scene.control.TitledPane;
import javafx.scene.layout.*;
import org.antlr.runtime.tree.Tree;

import java.util.List;

/**
 * Representation of a DafnyFunction in the call tree for the GUI
 * The method getNode() returns the View of this component
 */
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

    private boolean isHidden = false;

    private String headerText = "";

    private HighlightingHandler listener;

    /**
     * Fields of a Function
     */

    public DafnyFunction function;

    private List<DafnyTree> fPre;

    private List<DafnyTree> fPost;

    private DafnyTree fDecreasesClause;

    private List<DafnyTree> fArguments;

    private List<DafnyTree> fParams;

    private List<ParamValueObject> paramArgsList;

    public DafnyFunctionEntity(DafnyFunction f, DafnyTree t, HighlightingHandler listener, boolean call) {

        this.listener = listener;

        this.type = Type.FUNCTION;
        this.function = f;
        this.call = call;
        this.fPre = f.getRequiresClauses();
        this.fParams = f.getParameters();
        this.fPost = f.getEnsuresClauses();
        this.fDecreasesClause = f.getDecreasesClause();
        this.callTree = t;
        this.fArguments = callTree.getChildren().get(1).getChildren();
        this.headerText = "Function " + f.getName();
        if (!isCall()) {
            this.headerText = "Function " + f.getName() + " in " + t.getText();
        }


        paramArgsList = extractParams(fArguments, fParams);

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
        VBox vbox = new VBox();
        vbox.setBackground(WHITE_BACKGROUND);
        vbox.setSpacing(10);

        AnimatedLabel name;
        String nameText = "";

        if (isCall()) {
            nameText = headerText + " (line" + getUsageLine() + ")";

        } else {
            nameText = getEntity().getName() + getOuterEntity(callTree) + " in line" + getUsageLine();
        }
        name = new AnimatedLabel(nameText, callTree, listener );

        TitledPane tp = new TitledPane();

        vbox.getChildren().add(name);
        if (!paramArgsList.isEmpty()) {
            vbox.getChildren().add(createArgumentView(paramArgsList, listener));
        } else {
            vbox.getChildren().add(new Label("This function has no parameters"));
        }
        if (fPre.size() > 0) {
            vbox.getChildren().add(createPreconditionView(fPre, listener));
        }
        if (fPost.size() > 0) {
            vbox.getChildren().add(createPostconditionView(fPost, listener));
        }

        if (fDecreasesClause != null && isCall()) {
            vbox.getChildren().add(createDecreasesView(fDecreasesClause, listener));
        }
        tp.setText(nameText);
        tp.setContent(vbox);
        tp.setCollapsible(true);
        tp.setExpanded(false);
        return tp;
        //Accordion -> TitledPane->
        //return vbox;


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
