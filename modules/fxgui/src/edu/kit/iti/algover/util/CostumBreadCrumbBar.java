package edu.kit.iti.algover.util;

import com.google.common.collect.Lists;
import edu.kit.iti.algover.dafnystructures.DafnyFile;
import edu.kit.iti.algover.dafnystructures.DafnyMethod;
import javafx.collections.ObservableList;
import javafx.event.ActionEvent;
import javafx.event.EventHandler;
import javafx.scene.control.MenuButton;
import javafx.scene.control.MenuItem;
import javafx.scene.control.TreeItem;
import javafx.scene.layout.GridPane;
import javafx.scene.layout.HBox;

import java.util.ArrayList;
import java.util.List;
import java.util.function.Function;
import java.util.stream.Collectors;

/**
 * Created by jklamroth on 5/23/18.
 */
public class CostumBreadCrumbBar extends HBox {

    EventHandler<ActionEvent> actionEventEventHandler;


    public CostumBreadCrumbBar(TreeItem root) {

    }

    public void setSelectedCrumb(TreeItem item) {
        this.getChildren().clear();
        TreeItem i = item;
        List l = new ArrayList();
        while(i != null) {
            MenuButton b = new MenuButton(i.getValue().toString());
            if(i.getParent() != null) {
                for(Object ch : i.getParent().getChildren()) {
                    if(!ch.equals(i)) {
                        b.getItems().add(new MenuItem(((TreeItem)ch).getValue().toString()));
                        b.onActionProperty().setValue(actionEventEventHandler);
                    }
                }
            }
            l.add(b);
            i = i.getParent();
        }
        this.getChildren().addAll(Lists.reverse(l));
    }

    public void setOnCrumbAction(EventHandler<ActionEvent> handler) {
        this.actionEventEventHandler = handler;
    }
}
