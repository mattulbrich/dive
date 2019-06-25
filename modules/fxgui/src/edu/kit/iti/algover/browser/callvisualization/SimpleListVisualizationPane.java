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
    private ObservableList<CallEntity> calls = FXCollections.observableArrayList();

    private ListView<CallEntity> listview = new ListView<CallEntity>(calls);

    private CallVisualizationModel model;


    public SimpleListVisualizationPane(CallVisualizationModel model) {
        this.model = model;

        Collection<DafnyTree> callList = model.getCalls();
        DafnyDecl selectedDecl = model.getSelectedDeclaration();
        callList.forEach(dafnyTree -> calls.add(model.getDecl(dafnyTree).accept(new DafnyCallEntityVisitor(), dafnyTree)));

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
                                       // String accept = item.getCorrespondingDecl().accept(new DafnyDeclStringVisitor(), null);
                                        CallPane callPane = new CallPane(item);
                                        vbox.getChildren().add(callPane);

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
}
