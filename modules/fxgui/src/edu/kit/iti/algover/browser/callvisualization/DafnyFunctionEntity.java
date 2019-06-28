package edu.kit.iti.algover.browser.callvisualization;

import edu.kit.iti.algover.dafnystructures.DafnyDecl;
import edu.kit.iti.algover.dafnystructures.DafnyFunction;
import edu.kit.iti.algover.parser.DafnyParser;
import edu.kit.iti.algover.parser.DafnyTree;
import javafx.beans.property.SimpleStringProperty;
import javafx.collections.FXCollections;
import javafx.collections.ObservableList;
import javafx.scene.Node;
import javafx.scene.control.Label;
import javafx.scene.control.Separator;
import javafx.scene.control.TableColumn;
import javafx.scene.control.TableView;
import javafx.scene.control.cell.PropertyValueFactory;
import javafx.scene.layout.HBox;
import javafx.scene.layout.VBox;

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

        return vbox;


    }


    private Node createArgumentView() {
        Label name = new Label("Arguments: [Parameter name, Parameter type, Parameter value]");
        VBox vbox = new VBox(name);
        paramArgsList.forEach(paramValueObject -> {
            HBox hbox = new HBox();
            Label pname = new Label(paramValueObject.getName());
            Label ptype = new Label(paramValueObject.getType());
            Label pValue = new Label(paramValueObject.getValue());
            hbox.getChildren().addAll(pname, ptype,pValue);
            vbox.getChildren().add(hbox);
        });

        /*TableView<ParamValueObject> argumentTable = new TableView<ParamValueObject>();
        argumentTable.setEditable(false);

        TableColumn<ParamValueObject,String> paramName = new TableColumn<ParamValueObject,String>("Parameter name");
        TableColumn<ParamValueObject,String> paramType = new TableColumn<ParamValueObject,String>("Parameter type");
        TableColumn<ParamValueObject,String> argValue = new TableColumn<ParamValueObject,String>("Call value");
        argumentTable.getColumns().add(paramName);
        argumentTable.getColumns().add(paramType);
        argumentTable.getColumns().add(argValue);

        paramName.setCellValueFactory(new PropertyValueFactory<ParamValueObject,String>("name"));
        paramType.setCellValueFactory(new PropertyValueFactory<ParamValueObject,String>("type"));
        argValue.setCellValueFactory(new PropertyValueFactory<ParamValueObject,String>("value"));
        ObservableList<ParamValueObject> list = FXCollections.observableArrayList(this.paramArgsList);

        argumentTable.setItems(list);


        name.setOnMouseClicked(event -> {
            fArguments.size();
            fParams.size();
        });
        fArguments.size();*/

        return vbox;
    }

    @Override
    public String getString() {
        return this.headerText;
    }



    @Override
    public String getEntityName() {
        return this.getEntity().getName();
    }

    public class ParamValueObject{
        DafnyTree typeO;
        DafnyTree nameO;
        DafnyTree valueO;

        private final SimpleStringProperty type;
        private final SimpleStringProperty name;
        private final SimpleStringProperty value;

        public ParamValueObject(DafnyTree name, DafnyTree type, DafnyTree value) {
            this.typeO = type;
            this.nameO = name;
            this.valueO = value;
            this.type = new SimpleStringProperty(typeO.getText());
            this.name =  new SimpleStringProperty(nameO.getText());
            //todo abstieg im Baum
            this.value = new SimpleStringProperty(valueO.getText());

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
    }
}
