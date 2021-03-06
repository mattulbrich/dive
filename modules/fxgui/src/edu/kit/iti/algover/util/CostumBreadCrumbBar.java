/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.util;

import com.google.common.collect.Lists;
import javafx.application.Platform;
import javafx.beans.property.ObjectProperty;
import javafx.beans.property.SimpleObjectProperty;
import javafx.beans.value.ChangeListener;
import javafx.scene.control.MenuButton;
import javafx.scene.control.MenuItem;
import javafx.scene.control.TreeItem;
import javafx.scene.layout.HBox;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.function.Function;

/**
 * A breadcrumb bar consisting of several dropdown menus.
 * The menus are automatically created based on a {@link TreeItem}.
 * @author Jonas Klamroth (05/2018)
 */
public class CostumBreadCrumbBar<T> extends HBox {
    ObjectProperty<TreeItem<T>> selectedCrumb;
    TreeItem<T> root;
    Map<Object, TreeItem<T>> itemMap = new HashMap<Object, TreeItem<T>>();
    private Function<TreeItem<T>, String> getStringForTreeItem = item -> item.getValue().toString();


    public CostumBreadCrumbBar(TreeItem<T> root, ChangeListener<TreeItem<T>> changeListener) {
        this.root = root;
        addItemToMap(root);
        selectedCrumb = new SimpleObjectProperty<TreeItem<T>>();
        selectedCrumb.addListener(changeListener);
    }

    private void addItemToMap(TreeItem<T> item) {
        itemMap.put(item.getValue(), item);
        for(TreeItem<T> i : item.getChildren()) {
            addItemToMap(i);
        }
    }

    public void setSelectedCrumb(Object o) {
        TreeItem<T> item = itemMap.get(o);
        if(item == null) {
            throw new RuntimeException("Cannot select object " + o + " in BreadCrumbBar.");
        }
        setSelectedCrumb(item);
    }

    public void setSelectedCrumb(TreeItem<T> item) {
        this.getChildren().clear();
        TreeItem<T> i = item;
        List<MenuButton> l = new ArrayList<>();
        while (i != null) {
            MenuButton b = new MenuButton(getStringForTreeItem.apply(i));
            b.setMnemonicParsing(false);
            if (i.getParent() != null) {
                for (TreeItem<T> ch : i.getParent().getChildren()) {
                    MenuItem menuItem = new MenuItem(getStringForTreeItem.apply(ch));
                    menuItem.setMnemonicParsing(false);
                    menuItem.setOnAction(action -> {
                        selectedCrumb.set(ch);
                        Platform.runLater(() -> setSelectedCrumb(ch));
                    });
                    b.getItems().add(menuItem);
                }
            }
            l.add(b);
            i = i.getParent();
        }
        l.remove(l.size() - 1);

        while (item.getChildren().size() > 0) {
            MenuButton b = new MenuButton(getStringForTreeItem.apply(item.getChildren().get(0)));
            b.setMnemonicParsing(false);
            for (TreeItem<T> ch : item.getChildren()) {
                MenuItem menuItem = new MenuItem(getStringForTreeItem.apply(ch));
                menuItem.setMnemonicParsing(false);
                menuItem.setOnAction(action -> {
                    selectedCrumb.set(ch);
                    Platform.runLater(() -> setSelectedCrumb(ch));
                });
                b.getItems().add(menuItem);
            }
            l.add(0, b);
            item = item.getChildren().get(0);
        }
        this.getChildren().addAll(Lists.reverse(l));
    }

    public void setStringFactory(Function<TreeItem<T>, String> f) {
        this.getStringForTreeItem = f;
    }

    public TreeItem<T> getSelectedCrumb() {
        return selectedCrumb.get();
    }

    public TreeItem<T> getModel() {
        return root;
    }

    public void updateModel(TreeItem<T> newRoot) {
        root = newRoot;
        itemMap.clear();
        addItemToMap(root);
    }
}
