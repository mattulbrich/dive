package edu.kit.iti.algover.browser.callvisualization;

import edu.kit.iti.algover.dafnystructures.DafnyDecl;
import javafx.scene.Node;

public abstract class AbstractCallEntity {

    public enum Type {
        METHOD, FUNCTION, FIELD, CLASS
    }


    public abstract boolean isCall();


    public abstract  boolean isHidden();

    public abstract void setHidden(boolean hidden);

    public abstract String getHeaderText();

    public abstract int getUsageLine();

    public abstract Node getNode();

    public abstract Type getType();


    public abstract String getString();

    public abstract String getEntityName();

    public abstract DafnyDecl getEntity();
}
