package edu.kit.iti.algover.browser.callvisualization;

import de.jensd.fx.glyphs.materialdesignicons.MaterialDesignIcon;
import de.jensd.fx.glyphs.materialdesignicons.MaterialDesignIconView;
import edu.kit.iti.algover.dafnystructures.*;
import edu.kit.iti.algover.parser.DafnyTree;
import edu.kit.iti.algover.parser.DafnyTreeDefaultVisitor;
import javafx.collections.FXCollections;
import javafx.collections.ObservableList;
import javafx.event.EventHandler;
import javafx.scene.control.DialogPane;
import javafx.scene.control.Label;
import javafx.scene.control.ListCell;
import javafx.scene.control.ListView;
import javafx.scene.input.MouseEvent;
import javafx.scene.layout.VBox;
import javafx.util.Callback;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

/**
 * Pane that is deplayed if calls/callsites are requested
 */
public class SimpleListVisualizationPane extends DialogPane {
    private ObservableList<CallEntity> calls = FXCollections.observableArrayList();

    private ListView<CallEntity> listview = new ListView<CallEntity>(calls);

    private CallVisualizationModel model;


    public SimpleListVisualizationPane(CallVisualizationModel model) {
        this.model = model;

        Collection<DafnyTree> callList = model.getCalls();
        DafnyDecl selectedDecl = model.getSelectedDeclaration();
        callList.forEach(dafnyTree -> calls.add(new CallEntity(dafnyTree, model.getDecl(dafnyTree))));

//        callList.forEach(dafnyTree -> calls.add(new CallEntity(dafnyTree, model.getDecl(dafnyTree))));
        setHeaderText(computeHeaderText(selectedDecl));
        listview.setCellFactory(new Callback<ListView<CallEntity>, ListCell<CallEntity>>() {


            @Override
            public ListCell<CallEntity> call(ListView<CallEntity> treelist) {
                ListCell<CallEntity> cell = new ListCell<CallEntity>() {

                    protected void updateItem(final CallEntity item, boolean empty) {
                        super.updateItem(item, empty);
                        final VBox vbox = new VBox();
                        setGraphic(vbox);

                        if (item != null && getIndex() > -1) {
                            final Label labelHeader = new Label(item.getHeaderText());
                           // labelHeader.setGraphic(createArrowPath(20, false));
                            labelHeader.setGraphic(new MaterialDesignIconView(MaterialDesignIcon.ARROW_DOWN_DROP_CIRCLE));

                            labelHeader.setOnMouseClicked(new EventHandler<MouseEvent>() {
                                @Override
                                public void handle(MouseEvent me) {
                                    item.setHidden(item.isHidden() ? false : true);
                                    if (item.isHidden()) {
                                        labelHeader.setGraphic(new MaterialDesignIconView(MaterialDesignIcon.ARROW_DOWN_DROP_CIRCLE));
                                        vbox.getChildren().remove(vbox.getChildren().size() - 1);
                                    } else {
                                        labelHeader.setGraphic(new MaterialDesignIconView(MaterialDesignIcon.ARROW_UP_DROP_CIRCLE));
                                        String accept = item.getCorrespondingDecl().accept(new DafnyDeclStringVisitor(), null);
                                        vbox.getChildren().add(new Label(accept));
                                    }
                                }
                            });

                            vbox.getChildren().add(labelHeader);
                        }
                    }


                };
                return cell;
            }

        });
        this.setContent(listview);
        this.setMinWidth(600);

    }

    private String computeHeaderText(DafnyDecl selected) {
        String accept = selected.accept(new DafnyDeclStringVisitor(), null);
        return accept;
    }

    private class DafnyDeclStringVisitor implements DafnyDeclVisitor<String, Void> {

        @Override
        public String visit(DafnyClass cl, Void arg) {
            return "Class " + cl.getName();
        }

        @Override
        public String visit(DafnyMethod m, Void arg) {
            StringBuilder methodDeclaration = new StringBuilder();
            methodDeclaration.append("Method ");
            methodDeclaration.append(m.getName());
            List<DafnyTree> params = m.getParams();
            methodDeclaration.append("(");
            if (params.size() != 0) {
                for (DafnyTree parameter : params) {
                    switch (parameter.getText()) {
                        case "VAR":

                        case "ARGS":
                    }
                }
            }
            methodDeclaration.append(")");
            return methodDeclaration.toString();
        }

        @Override
        public String visit(DafnyFunction f, Void arg) {
            StringBuilder methodDeclaration = new StringBuilder();
            methodDeclaration.append("Function ");
            methodDeclaration.append(f.getName());
            List<DafnyTree> params = f.getParameters();
            methodDeclaration.append("(");
            if (params.size() != 0) {
                for (DafnyTree parameter : params) {
                    switch (parameter.getText()) {
                        case "VAR":
                           /* methodDeclaration.append("Parameter ");
                            ArrayList<String> strings = new ArrayList<>();
                            if(parameter.getChildren() != null) {
                                parameter.getChildren().forEach(dafnyTree -> {
                                    strings.addAll(dafnyTree.accept(new DafnyTreeCallEntityVisitor(), null));
                                });
                            }
                            strings.forEach(s -> {
                                methodDeclaration.append(s);
                                methodDeclaration.append(" ");
                            });*/
                        case "ARGS":
                            methodDeclaration.append("Argument ");
                            ArrayList<String> stringA = new ArrayList<>();

                            parameter.getChildren().forEach(dafnyTree -> {
                                stringA.addAll(dafnyTree.accept(new DafnyTreeCallEntityVisitor(), null));
                            });
                            stringA.forEach(s -> {
                                methodDeclaration.append(s);
                                methodDeclaration.append(" ");
                            });

                    }
                }
            }
            methodDeclaration.append(")");
            if(f.getDecreasesClause() != null){
                methodDeclaration.append("\nDecreases ");
                List<DafnyTree> children = f.getDecreasesClause().getChildren();
                for (DafnyTree child: children) {
                    List<String> accept = child.accept(new DafnyTreeCallEntityVisitor(), null);
                    methodDeclaration.append(accept);
                    methodDeclaration.append(" ");
                }
            }

            return methodDeclaration.toString();
        }

        @Override
        public String visit(DafnyField fi, Void arg) {
            return "Field " + fi.getType().getText() + " " + fi.getName();
        }

        @Override
        public String visit(DafnyFile file, Void arg) {
            return "File " + file.getName();
        }


    }

    private class DafnyTreeCallEntityVisitor extends DafnyTreeDefaultVisitor<List<String>, Void> {


        @Override
        public List<String> visitDefault(DafnyTree t, Void a) {
            List<String> list = new ArrayList<>();
            list.add(t.getText());
            if(t.getChildren() != null) {
                t.getChildren().forEach(dafnyTree -> {
                    list.addAll(dafnyTree.accept(this, a));
                });
            }
            return list;

        }

        @Override
        public List<String> visitTYPE(DafnyTree t, Void aVoid) {
            List<DafnyTree> children = t.getChildren();
            assert children.size()==1;
            return t.getChild(0).accept(this, aVoid);
        }
    }
}
