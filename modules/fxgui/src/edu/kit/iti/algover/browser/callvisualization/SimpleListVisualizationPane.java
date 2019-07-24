package edu.kit.iti.algover.browser.callvisualization;


import edu.kit.iti.algover.parser.DafnyTree;
import javafx.collections.FXCollections;
import javafx.collections.ObservableList;
import javafx.geometry.Insets;
import javafx.geometry.Orientation;
import javafx.scene.control.*;
import javafx.scene.layout.*;

import java.util.Collection;

/**
 * Pane that is displayed if calls/callsites are requested
 */
public class SimpleListVisualizationPane extends DialogPane {
    private ObservableList<AbstractCallEntity> calls = FXCollections.observableArrayList();

    private ObservableList<AbstractCallEntity> callsites = FXCollections.observableArrayList();


    private CallVisualizationModel model;

    private HighlightingHandler listener;


    public SimpleListVisualizationPane(CallVisualizationModel model, HighlightingHandler listener) {
        this.model = model;
        this.listener = listener;

        Collection<DafnyTree> callList = model.getCalls();
        callList.forEach(dafnyTree -> {
            AbstractCallEntity accept = model.getDecl(dafnyTree).accept(new DafnyCallEntityVisitor(listener, true), dafnyTree);
            calls.add(accept);
        });

        Collection<DafnyTree> callSiteList = model.getCallSites();
        callSiteList.forEach(dafnyTree -> {
            AbstractCallEntity accept = model.getDecl(dafnyTree).accept(new DafnyCallEntityVisitor(listener, false), dafnyTree);
            callsites.add(accept);
        });


        VBox listV = new VBox();
        listV.setPadding(new Insets(40,10,40,10));
        listV.setSpacing(15);

        if(!calls.isEmpty()){
            Label callCat = new Label("Calls:");
            callCat.setStyle("-fx-font-weight: bold; -fx-font-size: 14pt");
            listV.getChildren().add(callCat);
        }
        calls.forEach(abstractCallEntity -> {
            listV.getChildren().add(abstractCallEntity.getNode());

        });
        Separator e = new Separator(Orientation.HORIZONTAL);
        e.setPadding(new Insets(10,0,10,0));
        listV.getChildren().add(e);


        if(!callsites.isEmpty()){
            Label callCat = new Label("Callsites:");
            callCat.setStyle("-fx-font-weight: bold; -fx-font-size: 14pt;");
            listV.getChildren().add(callCat);
        }

        callsites.forEach(abstractCallEntity -> {
            listV.getChildren().add(abstractCallEntity.getNode());
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


        //listV.setMaxWidth(width);
        //ScrollPane sc = new ScrollPane(listV);
        BorderPane ac = new BorderPane();
        ac.setCenter(listV);
        ScrollPane sc = new ScrollPane(ac);
        this.setContent(sc);
        this.setMinWidth(400);

    }

}
