package edu.kit.iti.algover.browser.callvisualization;


import edu.kit.iti.algover.dafnystructures.*;
import edu.kit.iti.algover.parser.DafnyTree;
import javafx.collections.FXCollections;
import javafx.collections.ObservableList;
import javafx.geometry.Insets;
import javafx.geometry.Orientation;
import javafx.scene.control.*;
import javafx.scene.layout.*;
import javafx.scene.paint.Color;
import javafx.scene.text.Font;
import javafx.util.Callback;

import java.util.Collection;

/**
 * Pane that is displayed if calls/callsites are requested
 */
public class SimpleListVisualizationPane extends DialogPane {
    private ObservableList<AbstractCallEntity> calls = FXCollections.observableArrayList();

    private ObservableList<AbstractCallEntity> callsites = FXCollections.observableArrayList();

   // private ListView<AbstractCallEntity> listview = new ListView<AbstractCallEntity>(calls);

    private CallVisualizationModel model;

    private HighlightingHandler listener;


    public SimpleListVisualizationPane(CallVisualizationModel model, HighlightingHandler listener) {
        this.model = model;
        this.listener = listener;

        Collection<DafnyTree> callList = model.getCalls();
        callList.forEach(dafnyTree -> {
            AbstractCallEntity accept = model.getDecl(dafnyTree).accept(new DafnyCallEntityVisitor(listener), dafnyTree);
            calls.add(accept);
        });

        Collection<DafnyTree> callSiteList = model.getCallSites();
        callSiteList.forEach(dafnyTree -> {
            AbstractCallEntity accept = model.getDecl(dafnyTree).accept(new DafnyCallEntityVisitor(listener), dafnyTree);
            callsites.add(accept);
        });


        VBox listV = new VBox();
        listV.setPadding(new Insets(40,10,40,10));
        if(!calls.isEmpty()){
            Label callCat = new Label("Calls to");
            callCat.setStyle("-fx-font-weight: bold;");
            listV.getChildren().add(callCat);
        }
        calls.forEach(abstractCallEntity -> {
            listV.getChildren().add(abstractCallEntity.getNode());
            listV.getChildren().add(new Separator(Orientation.HORIZONTAL));
        });


        if(!callsites.isEmpty()){
            Label callCat = new Label("Callsites");
            callCat.setStyle("-fx-font-weight: bold;");
            listV.getChildren().add(callCat);

        }

        callsites.forEach(abstractCallEntity -> {
            listV.getChildren().add(abstractCallEntity.getNode());
            listV.getChildren().add(new Separator(Orientation.HORIZONTAL));
        });
     /*   listview.setCellFactory(new Callback<ListView<AbstractCallEntity>, ListCell<AbstractCallEntity>>() {
            @Override
            public ListCell<AbstractCallEntity> call(ListView<AbstractCallEntity> treelist) {
                ListCell<AbstractCallEntity> cell = new ListCell<AbstractCallEntity>() {

                    protected void updateItem(final AbstractCallEntity item, boolean empty) {
                        super.updateItem(item, empty);
                        final VBox vbox = new VBox();
                        setGraphic(vbox);

                        if (item != null && getIndex() > -1) {
                            final Label labelHeader = new Label(item.isCall()? "Call "+ item.getHeaderText(): "Callsite "+item.getHeaderText());
                            labelHeader.setStyle("-fx-font-weight: bold;");
                           // labelHeader.setGraphic(createArrowPath(20, false));
                            //labelHeader.setGraphic(new MaterialDesignIconView(MaterialDesignIcon.ARROW_DOWN_DROP_CIRCLE));

                          /*  labelHeader.setOnMouseClicked(new EventHandler<MouseEvent>() {
                                @Override
                                public void handle(MouseEvent me) {
                                    item.setHidden(item.isHidden() ? false : true);
                                    if (item.isHidden()) {
                                        labelHeader.setGraphic(new MaterialDesignIconView(MaterialDesignIcon.ARROW_DOWN_DROP_CIRCLE));
                                        vbox.getChildren().remove(vbox.getChildren().size() - 1);
                                    } else {
                                        labelHeader.setGraphic(new MaterialDesignIconView(MaterialDesignIcon.ARROW_UP_DROP_CIRCLE));
                                        vbox.getChildren().add(item.getNode());

                                    }
                                }
                            });*/

                        /*    vbox.getChildren().add(labelHeader);
                            vbox.getChildren().add(item.getNode());
                           // vbox.setBorder(new Border(new BorderStroke(Color.GRAY, BorderStrokeStyle.SOLID, null, new BorderWidths(1))));
                        }
                    }


                };
                return cell;
            }

        });
        this.setContent(listview);*/
        this.setContent(listV);
        this.setMinWidth(600);

    }

}
