package edu.kit.iti.algover.browser.callvisualization;

import edu.kit.iti.algover.dafnystructures.DafnyDecl;
import edu.kit.iti.algover.parser.DafnyParser;
import edu.kit.iti.algover.parser.DafnyTree;
import edu.kit.iti.algover.parser.DafnyTreeDefaultVisitor;
import javafx.beans.property.SimpleStringProperty;
import javafx.geometry.Insets;
import javafx.geometry.Orientation;
import javafx.scene.Node;
import javafx.scene.control.Label;
import javafx.scene.control.Separator;
import javafx.scene.layout.*;
import javafx.scene.paint.Color;
import net.miginfocom.layout.AC;
import net.miginfocom.layout.LC;
import org.antlr.runtime.Token;
import org.antlr.runtime.tree.Tree;
import org.tbee.javafx.scene.layout.MigPane;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

public abstract class AbstractCallEntity {

    public enum Type {
        METHOD, FUNCTION, FIELD, CLASS
    }

    public static Background WHITE_BACKGROUND = new Background(new BackgroundFill(Color.WHITE, null, null));
    public static Background SELECTED_LABEL = new Background(new BackgroundFill(Color.LIGHTCYAN, null, null));



    public abstract boolean isCall();


    public abstract  boolean isHidden();

    public abstract void setHidden(boolean hidden);

    public abstract String getHeaderText();

    public abstract int getUsageLine();

    public abstract Node getNode();

    public abstract Type getType();


    public abstract String getString();

    public abstract String getEntityName();

    public abstract DafnyDecl getEntity();

     Node createDecreasesView(DafnyTree decreasesClause, HighlightingHandler listener) {
        VBox vbox = new VBox();
        Label header = new Label("Decreases Clause:");
         header.setStyle("-fx-font-weight: bold");

        AnimatedLabel decrs = new AnimatedLabel(decreasesClause.accept(new DafnyFunctionEntity.DafnySpecTreeStringVisitor(), null), decreasesClause, listener);
        decrs.setPadding(new Insets(0,0,0,20));
        vbox.getChildren().addAll(header, decrs);
        return vbox;
    }

     Node createPreconditionView(List<DafnyTree> preconditions, HighlightingHandler listener) {
        return createContractView(preconditions, listener, "Preconditions:");

    }

     Node createPostconditionView(List<DafnyTree> postconditions, HighlightingHandler listener) {
        return createContractView(postconditions, listener, "Postconditions:");

    }

    private Node createContractView(List<DafnyTree> conditions, HighlightingHandler listener, String title){
        VBox vbox = new VBox();
        AnimatedLabel header = new AnimatedLabel(title);
        header.setStyle("-fx-font-weight: bold");
        vbox.getChildren().add(header);
        conditions.forEach(dafnyTree -> {
            AnimatedLabel l = new AnimatedLabel(dafnyTree.accept(new DafnyFunctionEntity.DafnySpecTreeStringVisitor(), null), dafnyTree, listener);
            l.setPadding(new Insets(0,0,0,20));
            vbox.getChildren().add(l);
        });


        return vbox;
    }

    /***
     * Creates the view containing the Parameter information
     * @param paramArgsList
     * @param listener
     * @return
     */
    Node createArgumentView(List<DafnyFunctionEntity.ParamValueObject> paramArgsList, HighlightingHandler listener) {

        MigPane mp = new MigPane(new LC().wrapAfter(5).gridGapX("10px"), new AC().grow(1).size("pref",0,2,3,4));
        mp.setBorder(new Border(new BorderStroke(Color.GRAY, BorderStrokeStyle.SOLID, null, new BorderWidths(1))));
        mp.add(new Label("Parameter Name"));
        Separator node = new Separator(Orientation.VERTICAL);
        mp.add(node);
        mp.add(new Label("Type"));
        mp.add(new Separator(Orientation.VERTICAL));
        mp.add(new Label("Argument on call"));
        paramArgsList.forEach(paramValueObject -> {
            DafnyTree nameTree = paramValueObject.getNameTree();
            AnimatedLabel pname = new AnimatedLabel(paramValueObject.getName(), nameTree, listener);

            Separator s = new Separator(Orientation.VERTICAL);
            s.setMinHeight(pname.getMinHeight());
            s.setMaxHeight(pname.getMaxHeight());
            s.setPrefHeight(pname.getPrefHeight());

            DafnyTree typeTree = paramValueObject.getTypeTree();
            AnimatedLabel ptype = new AnimatedLabel(paramValueObject.getType(), typeTree, listener);

            Separator s1 = new Separator(Orientation.VERTICAL);
            s1.setMinHeight(ptype.getMinHeight());
            s1.setMaxHeight(ptype.getMaxHeight());
            s1.setPrefHeight(ptype.getPrefHeight());

            DafnyTree valueTree = paramValueObject.getValueTree();
            AnimatedLabel pValue = new AnimatedLabel(paramValueObject.getValue(), valueTree, listener);
            mp.add(pname);
            mp.add(s);
            mp.add(ptype);
            mp.add(s1);
            mp.add(pValue);
        });
        return mp;

    }


    /**
     * Extract a list of objects that contain parameters and their values upon call
     * @param fArguments The DafnyTrees representing the arguments on call
     * @param fParams The DafnyTrees representing the parameter declaration
     * @return List of ParamValueObjects containing the relations between parameter declaration and the values upon call
     */
     List<ParamValueObject> extractParams(List<DafnyTree> fArguments, List<DafnyTree> fParams) {
        //Name, type, value
        List<ParamValueObject> list = new ArrayList<>();
        Iterator<DafnyTree> argsIterator = fArguments.iterator();
        Iterator<DafnyTree> paramsIterator = fParams.iterator();
        while(paramsIterator.hasNext()){
            DafnyTree params = paramsIterator.next();
            DafnyTree arg = argsIterator.next();
            List<DafnyTree> childrenWithType = params.getChildrenWithType(DafnyParser.TYPE);
            assert childrenWithType.size() == 1;
            list.add(new ParamValueObject(params.getChild(0), childrenWithType.get(0).getChild(0), arg));
        }
        return list;

    }

    /**
     * Visitor to extract the String representation of different Dafny entities
     */
    public class DafnySpecTreeStringVisitor extends DafnyTreeDefaultVisitor<String, Void> {

        @Override
        public String visitDefault(DafnyTree t, Void arg) {
            StringBuilder text = new StringBuilder();
            String text1 = t.getText();
            String currentNode = text1;
            if(t.getChildren().size() == 2){
                String accept = t.getChild(0).accept(this, arg);
                text.append(accept);
                text.append(currentNode);
                text.append(t.getChild(1).accept(this, arg));
            } else {
                text.append(currentNode);
                t.getChildren().forEach(dafnyTree -> text.append(dafnyTree.accept(this, arg)));
            }
            return text.toString();

        }

        @Override
        public String visitDECREASES(DafnyTree t, Void aVoid) {
            StringBuilder sb = new StringBuilder();
            t.getChildren().forEach(dafnyTree -> sb.append(dafnyTree.accept(this, aVoid)));
            return sb.toString();
        }

        @Override
        public String visitARGS(DafnyTree t, Void aVoid) {
            StringBuilder sb = new StringBuilder();
            sb.append("(");
            Iterator<DafnyTree> iterator = t.getChildren().iterator();
            while (iterator.hasNext()){
                DafnyTree next = iterator.next();
                sb.append(next.accept(this, aVoid));
                if(iterator.hasNext()){
                    sb.append(", ");
                }
            }
            sb.append(")");
            return sb.toString();
        }

        @Override
        public String visitCALL(DafnyTree t, Void aVoid) {
            StringBuilder sb = new StringBuilder();
            t.getChildren().forEach(dafnyTree -> sb.append(dafnyTree.accept(this, aVoid)));
            return sb.toString();
        }

        @Override
        public String visitREQUIRES(DafnyTree t, Void aVoid) {
            StringBuilder sb = new StringBuilder();
            sb.append("requires (");
            Iterator<DafnyTree> iterator = t.getChildren().iterator();
            while (iterator.hasNext()){
                DafnyTree next = iterator.next();
                sb.append(next.accept(this, aVoid));
            }
            sb.append(")");
            return sb.toString();

        }

        @Override
        public String visitENSURES(DafnyTree t, Void aVoid) {
                StringBuilder sb = new StringBuilder();
                sb.append("ensures (");
                Iterator<DafnyTree> iterator = t.getChildren().iterator();
                while (iterator.hasNext()){
                    DafnyTree next = iterator.next();
                    sb.append(next.accept(this, aVoid));
                }
                sb.append(")");
                return sb.toString();


        }
    }

    /**
     * Helper Object encapsulating Argument and parameter relations
     */
    public class ParamValueObject{
        private DafnyTree typeO;
        private DafnyTree nameO;
        private DafnyTree valueO;

        private final SimpleStringProperty type;
        private final SimpleStringProperty name;
        private final SimpleStringProperty value;

        public ParamValueObject(DafnyTree name, DafnyTree type, DafnyTree value) {
            this.typeO = type;
            this.nameO = name;
            this.valueO = value;
            this.type = new SimpleStringProperty(typeO.getText());
            this.name =  new SimpleStringProperty(nameO.getText());
            String accept = valueO.accept(new DafnyTreeStringVisitor(), null);
            this.value = new SimpleStringProperty(accept);

        }

        public DafnyTree getTypeTree() {
            return typeO;
        }

        public DafnyTree getNameTree() {
            return nameO;
        }

        public DafnyTree getValueTree() {
            return valueO;
        }

        public String getType() {
            return type.get();
        }

        public String getName() {
            return name.get();
        }

        public String getValue() {
            return value.get();
        }


        public class DafnyTreeStringVisitor extends DafnyTreeDefaultVisitor<String, Void>{

            @Override
            public String visitDefault(DafnyTree t, Void arg) {
                StringBuilder text = new StringBuilder();
                java.lang.String text1 = t.getText();
                String currentNode = text1;
                if(t.getChildren().size() == 2){
                    String accept = t.getChild(0).accept(this, arg);
                    text.append(accept);
                    text.append(currentNode);
                    text.append(t.getChild(1).accept(this, arg));
                } else {
                    text.append(currentNode);
                    t.getChildren().forEach(dafnyTree -> text.append(dafnyTree.accept(this, arg)));
                }
                return text.toString();

            }
        }
    }

    /**
     * Find the outer entity of a DafnyTree if a callsite needs to be displayed
     * @param callTree Method or Function that was called in a context
     * @return the String representation of the outer context
     */
    String getOuterEntity(DafnyTree callTree) {
        StringBuilder sb = new StringBuilder();
        Token start = callTree.getStartToken();
        Token end = callTree.getStopToken();
        DafnyTree unit = null;

        Tree parent =  callTree.getParent();
        while(parent.getParent() != null ){
            if(parent.getType() == DafnyParser.METHOD || parent.getType() == DafnyParser.FUNCTION) {
                unit = (DafnyTree) parent;
                Token startToken = unit.getStartToken();
                Token stopToken = unit.getStopToken();
                if (start.getLine() > startToken.getLine()
                        && end.getLine() < stopToken.getLine()
                        && !start.equals(startToken))
                    break;
                else
                    parent = parent.getParent();
            } else {
                parent = parent.getParent();
            }
        }
        if(unit != null) {
            switch (unit.getType()) {
                case DafnyParser.METHOD:
                    sb.append(" is called in Method ");
                    sb.append(unit.getChild(0).getText());
                    break;
                case DafnyParser.FUNCTION:
                    sb.append(" is called in Function ");
                    sb.append(unit.getChild(0).getText());
                    break;
                default:
            }

        }
        return sb.toString();
    }


}
