package edu.kit.iti.algover.browser.callvisualization;

import edu.kit.iti.algover.dafnystructures.DafnyDecl;
import edu.kit.iti.algover.dafnystructures.DafnyFunction;
import edu.kit.iti.algover.parser.DafnyParser;
import edu.kit.iti.algover.parser.DafnyTree;
import edu.kit.iti.algover.parser.DafnyTreeDefaultVisitor;
import javafx.beans.property.SimpleStringProperty;
import javafx.scene.Node;
import javafx.scene.control.Label;
import javafx.scene.layout.HBox;
import javafx.scene.layout.VBox;
import net.miginfocom.layout.AC;
import net.miginfocom.layout.LC;
import org.tbee.javafx.scene.layout.MigPane;

import java.util.ArrayList;
import java.util.Iterator;
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
        this.fDecreasesClause = f.getDecreasesClause();
        this.callTree = t;
        this.fArguments = callTree.getChildren().get(1).getChildren();
        this.headerText = "Function "+f.getName();


        paramArgsList = extractParams();

    }

    private List<ParamValueObject> extractParams() {
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
        vbox.getChildren().add(createArgumentView());
        if(fPre.size() > 0) {
            vbox.getChildren().add(createPreconditionView());
        }
        if(fPost.size() > 0){

        }

        if(fDecreasesClause != null){
            vbox.getChildren().add(createDecreasesView());
        }
        return vbox;


    }

    private Node createDecreasesView() {
        VBox vbox = new VBox();
        Label header = new Label("Decreases Clause: " + fDecreasesClause.accept(new DafnySpecTreeStringVisitor(), null));
        header.setOnMouseClicked(event -> listener.onRequestHighlight(fDecreasesClause.getFilename(), fDecreasesClause.getStartToken(), fDecreasesClause.getStopToken()));
        vbox.getChildren().add(header);
        return vbox;
    }

    private Node createPreconditionView() {
        VBox vbox = new VBox();
        Label header = new Label("Preconditions:");
        vbox.getChildren().add(header);
        fPre.forEach(dafnyTree -> {
            Label l = new Label(dafnyTree.accept(new DafnySpecTreeStringVisitor(), null));
            l.setOnMouseClicked(event -> listener.onRequestHighlight(dafnyTree.getFilename(), dafnyTree.getStartToken(), dafnyTree.getStopToken()));
            vbox.getChildren().add(l);
        });


        return vbox;
    }


    private Node createArgumentView() {
        MigPane mp = new MigPane(new LC().wrapAfter(3).gridGapX("10px"), new AC().grow(1,3).size("pref",1,2));
        mp.add(new Label("Parameter Name"));
        mp.add(new Label("Type"));
        mp.add(new Label("Argument on call"));
        paramArgsList.forEach(paramValueObject -> {
            Label pname = new Label(paramValueObject.getName());
            pname.setOnMouseClicked(event -> {
                DafnyTree nameTree = paramValueObject.getNameTree();
                listener.onRequestHighlight(nameTree.getFilename(), nameTree.getStartToken(), nameTree.getStopToken());
            });
            Label ptype = new Label(paramValueObject.getType());
            ptype.setOnMouseClicked(event -> {
                DafnyTree typeTree = paramValueObject.getTypeTree();
                listener.onRequestHighlight(typeTree.getFilename(), typeTree.getStartToken(), typeTree.getStopToken());
            });

            Label pValue = new Label(paramValueObject.getValue());
            pValue.setOnMouseClicked(event -> {
                DafnyTree valueTree = paramValueObject.getValueTree();
                listener.onRequestHighlight(valueTree.getFilename(), valueTree.getStartToken(), valueTree.getStopToken());
            });

            mp.add(pname);
            mp.add(ptype);
            mp.add(pValue);
        });
        return mp;

    }

    @Override
    public String getString() {
        return this.headerText;
    }



    @Override
    public String getEntityName() {
        return this.getEntity().getName();
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


    public class DafnySpecTreeStringVisitor extends DafnyTreeDefaultVisitor<String, Void>{

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
}
