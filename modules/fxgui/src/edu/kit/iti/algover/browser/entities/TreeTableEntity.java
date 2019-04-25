package edu.kit.iti.algover.browser.entities;

import edu.kit.iti.algover.dafnystructures.DafnyFile;
import javafx.beans.Observable;
import javafx.beans.property.IntegerProperty;
import javafx.beans.property.SimpleIntegerProperty;
import javafx.beans.property.SimpleStringProperty;
import javafx.beans.property.StringProperty;

import java.util.List;

/**
 * Created by philipp on 26.06.17.
 */
public abstract class TreeTableEntity {

    private final StringProperty text;
    private final DafnyFile location;
    private final IntegerProperty numberChildren;
    private final IntegerProperty provenChildren;
    private final List<TreeTableEntity> children;

    public TreeTableEntity(String text, DafnyFile location, List<TreeTableEntity> children) {
        this.text = new SimpleStringProperty(text);
        this.children = children;
        this.location = location;
        this.numberChildren = new SimpleIntegerProperty(
                children.stream()
                        .map(TreeTableEntity::getNumberChildren)
                        .reduce(0, (x, y) -> x + y));
        this.provenChildren = new SimpleIntegerProperty(
                children.stream()
                        .map(TreeTableEntity::getProvenChildren)
                        .reduce(0, (x, y) -> x + y));
        for(TreeTableEntity ch : children) {
            ch.provenChildrenProperty().addListener((obs, old, nu) -> {
                int diff = old.intValue() - nu.intValue();
                this.provenChildren.setValue(this.provenChildren.get() - diff);
            });
        }
    }

    private void updateProvenChildren(Observable observable) {

    }

    public abstract <T> T accept(TreeTableEntityVisitor<T> visitor);

    public DafnyFile getLocation() {
        return location;
    }

    public String getText() {
        return text.get();
    }

    public StringProperty textProperty() {
        return text;
    }

    public int getNumberChildren() {
        return numberChildren.get();
    }

    public IntegerProperty numberChildrenProperty() {
        return numberChildren;
    }

    public int getProvenChildren() {
        return provenChildren.get();
    }

    public IntegerProperty provenChildrenProperty() {
        return provenChildren;
    }

    @Override
    public String toString() {
        return "TreeTableEntity{" +
                "name=" + text.get() +
                '}';
    }

    public List<TreeTableEntity> getChildren() {
        return children;
    }
}
