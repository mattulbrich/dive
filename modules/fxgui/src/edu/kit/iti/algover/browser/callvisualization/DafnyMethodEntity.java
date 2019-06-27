package edu.kit.iti.algover.browser.callvisualization;

import edu.kit.iti.algover.dafnystructures.DafnyDecl;
import edu.kit.iti.algover.dafnystructures.DafnyMethod;
import edu.kit.iti.algover.parser.DafnyTree;
import javafx.scene.Node;

public class DafnyMethodEntity extends AbstractCallEntity {
    public DafnyMethodEntity(DafnyMethod m, DafnyTree arg) {
        super();
    }

    @Override
    public boolean isCall() {
        return false;
    }

    @Override
    public boolean isHidden() {
        return false;
    }

    @Override
    public void setHidden(boolean hidden) {

    }

    @Override
    public String getHeaderText() {
        return null;
    }

    @Override
    public int getUsageLine() {
        return 0;
    }

    @Override
    public Node getNode() {
        return null;
    }

    @Override
    public Type getType() {
        return null;
    }

    @Override
    public String getString() {
        return null;
    }

    @Override
    public String getEntityName() {
        return null;
    }

    @Override
    public DafnyDecl getEntity() {
        return null;
    }
}
