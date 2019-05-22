package edu.kit.iti.algover.browser.callvisualization;

import com.jfoenix.controls.JFXTreeView;
import edu.kit.iti.algover.parser.DafnyTree;
import javafx.scene.Node;
import javafx.scene.control.TreeItem;

public class CallEntity {
    private DafnyTree callTree;


    private boolean call = false;

    private boolean isHidden = true;

    private String headerText = "";

    public CallEntity(DafnyTree tree){
        this.callTree = tree;
        if(tree.getText().equals("CALL")){
            call = true;
        }
        headerText = tree.getChild(0).getText()+ " in line "+tree.getStartToken().getLine();
    }

    public boolean isCall() {
        return call;
    }


    public boolean isHidden() {
        return isHidden;
    }

    public void setHidden(boolean hidden) {
        isHidden = hidden;
    }

    public String getHeaderText() {
        return headerText;
    }


    public JFXTreeView<DafnyTree> getTreeVisualization() {

        TreeItem<DafnyTree> item = new TreeItem<DafnyTree>();
        callTree.accept(new DafnyTreeItemVisitor(), item);
        JFXTreeView<DafnyTree> tree = new JFXTreeView<DafnyTree>(item);
        return tree;
    }
}
