package edu.kit.iti.algover.browser.callvisualization;

import edu.kit.iti.algover.dafnystructures.DafnyDecl;
import edu.kit.iti.algover.parser.DafnyParser;
import edu.kit.iti.algover.parser.DafnyTree;
import edu.kit.iti.algover.parser.DafnyTreeDefaultVisitor;
import javafx.beans.property.SimpleStringProperty;
import javafx.geometry.Orientation;
import javafx.scene.Node;
import javafx.scene.control.Label;
import javafx.scene.control.Separator;
import javafx.scene.layout.*;
import javafx.scene.paint.Color;
import net.miginfocom.layout.AC;
import net.miginfocom.layout.LC;
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
        AnimatedLabel decrs = new AnimatedLabel(decreasesClause.accept(new DafnyFunctionEntity.DafnySpecTreeStringVisitor(), null));
        header.setStyle("-fx-font-weight: bold");
        decrs.setOnMouseClicked(event -> listener.onRequestHighlight(decreasesClause.getFilename(), decreasesClause.getStartToken(), decreasesClause.getStopToken()));
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

            AnimatedLabel l = new AnimatedLabel(dafnyTree.accept(new DafnyFunctionEntity.DafnySpecTreeStringVisitor(), null));
            l.setOnMouseClicked(event -> listener.onRequestHighlight(dafnyTree.getFilename(), dafnyTree.getStartToken(), dafnyTree.getStopToken()));
            vbox.getChildren().add(l);
        });


        return vbox;
    }

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
            AnimatedLabel pname = new AnimatedLabel(paramValueObject.getName());
            pname.setOnMouseClicked(event -> {
                DafnyTree nameTree = paramValueObject.getNameTree();
                listener.onRequestHighlight(nameTree.getFilename(), nameTree.getStartToken(), nameTree.getStopToken());
            });
            Separator s = new Separator(Orientation.VERTICAL);
            s.setMinHeight(pname.getMinHeight());
            s.setMaxHeight(pname.getMaxHeight());
            s.setPrefHeight(pname.getPrefHeight());

            AnimatedLabel ptype = new AnimatedLabel(paramValueObject.getType());
            ptype.setOnMouseClicked(event -> {
                DafnyTree typeTree = paramValueObject.getTypeTree();
                listener.onRequestHighlight(typeTree.getFilename(), typeTree.getStartToken(), typeTree.getStopToken());
            });

            Separator s1 = new Separator(Orientation.VERTICAL);
            s1.setMinHeight(ptype.getMinHeight());
            s1.setMaxHeight(ptype.getMaxHeight());
            s1.setPrefHeight(ptype.getPrefHeight());

            AnimatedLabel pValue = new AnimatedLabel(paramValueObject.getValue());
            pValue.setOnMouseClicked(event -> {
                DafnyTree valueTree = paramValueObject.getValueTree();
                listener.onRequestHighlight(valueTree.getFilename(), valueTree.getStartToken(), valueTree.getStopToken());
            });

            mp.add(pname);
            mp.add(s);
            mp.add(ptype);
            mp.add(s1);
            mp.add(pValue);
//            mp.add(s2);
        });
        return mp;

    }



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
     * Visitor to extract the String representation of different artifacts
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


}
