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
 * Pane that is displayed if calls/callsites are requested
 */
public class SimpleListVisualizationPane extends DialogPane {
    private ObservableList<AbstractCallEntity> calls = FXCollections.observableArrayList();

    private ListView<AbstractCallEntity> listview = new ListView<AbstractCallEntity>(calls);

    private CallVisualizationModel model;

    private HighlightingHandler listener;


    public SimpleListVisualizationPane(CallVisualizationModel model, HighlightingHandler listener) {
        this.model = model;
        this.listener = listener;

        Collection<DafnyTree> callList = model.getCalls();
        DafnyDecl selectedDecl = model.getSelectedDeclaration();
        callList.forEach(dafnyTree -> {
            AbstractCallEntity accept = model.getDecl(dafnyTree).accept(new DafnyCallEntityVisitor(listener), dafnyTree);
            calls.add(accept);
        });

        //setHeaderText(computeHeaderText(selectedDecl));
        listview.setCellFactory(new Callback<ListView<AbstractCallEntity>, ListCell<AbstractCallEntity>>() {


            @Override
            public ListCell<AbstractCallEntity> call(ListView<AbstractCallEntity> treelist) {
                ListCell<AbstractCallEntity> cell = new ListCell<AbstractCallEntity>() {

                    protected void updateItem(final AbstractCallEntity item, boolean empty) {
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
                                        vbox.getChildren().add(item.getNode());

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

}
