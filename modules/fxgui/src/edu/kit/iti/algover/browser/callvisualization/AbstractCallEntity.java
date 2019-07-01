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

    public Node createDecreasesView(DafnyTree decreasesClause, HighlightingHandler listener) {
        VBox vbox = new VBox();
        Label header = new Label("Decreases Clause: \n" + decreasesClause.accept(new DafnyFunctionEntity.DafnySpecTreeStringVisitor(), null));
        header.setOnMouseClicked(event -> listener.onRequestHighlight(decreasesClause.getFilename(), decreasesClause.getStartToken(), decreasesClause.getStopToken()));
        vbox.getChildren().add(header);
        return vbox;
    }

    public Node createPreconditionView(List<DafnyTree> preconditions, HighlightingHandler listener) {
        return createContractView(preconditions, listener, "Preconditions:");

    }

    public Node createPostconditionView(List<DafnyTree> postconditions, HighlightingHandler listener) {
        return createContractView(postconditions, listener, "Postconditions:");

    }

    private Node createContractView(List<DafnyTree> conditions, HighlightingHandler listener, String title){
        VBox vbox = new VBox();
        Label header = new Label(title);
        vbox.getChildren().add(header);
        conditions.forEach(dafnyTree -> {
            Label l = new Label(dafnyTree.accept(new DafnyFunctionEntity.DafnySpecTreeStringVisitor(), null));
            l.setOnMouseClicked(event -> listener.onRequestHighlight(dafnyTree.getFilename(), dafnyTree.getStartToken(), dafnyTree.getStopToken()));
            vbox.getChildren().add(l);
        });


        return vbox;
    }

    public Node createArgumentView(List<DafnyFunctionEntity.ParamValueObject> paramArgsList, HighlightingHandler listener) {

        MigPane mp = new MigPane(new LC().wrapAfter(6).gridGapX("10px"), new AC().grow(1,4).size("pref",1,2,3,5));
        mp.setBorder(new Border(new BorderStroke(Color.GRAY, BorderStrokeStyle.SOLID, null, new BorderWidths(1))));
        mp.add(new Label("Parameter Name"));
        Separator node = new Separator(Orientation.VERTICAL);
        mp.add(node);
        mp.add(new Label("Type"));
        mp.add(new Separator(Orientation.VERTICAL));
        mp.add(new Label("Argument on call"));
        mp.add(new Separator(Orientation.VERTICAL));
        paramArgsList.forEach(paramValueObject -> {
            Label pname = new Label(paramValueObject.getName());
            pname.setOnMouseClicked(event -> {
                DafnyTree nameTree = paramValueObject.getNameTree();
                listener.onRequestHighlight(nameTree.getFilename(), nameTree.getStartToken(), nameTree.getStopToken());
            });
            Separator s = new Separator(Orientation.VERTICAL);
            s.setMinHeight(pname.getMinHeight());
            s.setMaxHeight(pname.getMaxHeight());
            s.setPrefHeight(pname.getPrefHeight());

            Label ptype = new Label(paramValueObject.getType());
            /*ptype.setBorder(new Border(new BorderStroke(Color.RED, Color.RED, Color.RED, Color.RED,
                    BorderStrokeStyle.SOLID, BorderStrokeStyle.SOLID, BorderStrokeStyle.NONE, BorderStrokeStyle.SOLID,
                    CornerRadii.EMPTY, new BorderWidths(5), Insets.EMPTY)));*/
            ptype.setOnMouseClicked(event -> {
                DafnyTree typeTree = paramValueObject.getTypeTree();
                listener.onRequestHighlight(typeTree.getFilename(), typeTree.getStartToken(), typeTree.getStopToken());
            });

            Separator s1 = new Separator(Orientation.VERTICAL);
            s1.setMinHeight(ptype.getMinHeight());
            s1.setMaxHeight(ptype.getMaxHeight());
            s1.setPrefHeight(ptype.getPrefHeight());

            Label pValue = new Label(paramValueObject.getValue());
            pValue.setOnMouseClicked(event -> {
                DafnyTree valueTree = paramValueObject.getValueTree();
                listener.onRequestHighlight(valueTree.getFilename(), valueTree.getStartToken(), valueTree.getStopToken());
            });

            Separator s2 = new Separator(Orientation.VERTICAL);
            s2.setMinHeight(pValue.getMinHeight());
            s2.setMaxHeight(pValue.getMaxHeight());
            s2.setPrefHeight(pValue.getPrefHeight());

            mp.add(pname);
            mp.add(s);
            mp.add(ptype);
            mp.add(s1);
            mp.add(pValue);
            mp.add(s2);
        });
        return mp;

    }

    public List<ParamValueObject> extractParams(List<DafnyTree> fArguments, List<DafnyTree> fParams) {
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
    public class DafnySpecTreeStringVisitor extends DafnyTreeDefaultVisitor<String, Void> {

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
