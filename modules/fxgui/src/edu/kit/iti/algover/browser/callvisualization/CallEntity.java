package edu.kit.iti.algover.browser.callvisualization;

import com.jfoenix.controls.JFXTreeCell;
import com.jfoenix.controls.JFXTreeView;
import edu.kit.iti.algover.dafnystructures.DafnyDecl;
import edu.kit.iti.algover.parser.DafnyTree;
import javafx.scene.control.TextArea;
import javafx.scene.control.TreeCell;
import javafx.scene.control.TreeItem;
import javafx.scene.control.TreeView;
import javafx.scene.control.cell.TextFieldTreeCell;
import javafx.scene.layout.VBox;
import javafx.util.Callback;
import javafx.util.StringConverter;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

/**
 * Entity of a call/callsite that is displayed in the list view (viewmodel)
 */
public class CallEntity {
    private DafnyTree callTree;

    public DafnyDecl getCorrespondingDecl() {
        return correspondingDecl;
    }

    private DafnyDecl correspondingDecl;

    private boolean call = false;

    private boolean isHidden = true;

    private String headerText = "";

    public CallEntity(DafnyTree tree, DafnyDecl correspondingDecl){
        this.callTree = tree;
        this.correspondingDecl = correspondingDecl;
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


   /* @Deprecated
    public JFXTreeView<DafnyTree> getTreeVisualization() {
        TreeItem<DafnyTree> root = new TreeItem<>();
        TreeItem<DafnyTree> accept = correspondingDecl.getRepresentation().accept(new DafnyTreeItemVisitor(), root);
        JFXTreeView<DafnyTree> tree = new JFXTreeView<DafnyTree>(root);
        tree.setCellFactory(tv -> new TreeCell<DafnyTree>()
        {
            @Override
            protected void updateItem(DafnyTree item, boolean empty)
            {
                super.updateItem(item, empty);

                if (item != null)
                {
                    setText(item.getText());
                }
            }
        });

        return tree;
    }*/

    public VBox getDetailPane() {
        VBox vbox = new VBox();
        TextArea a = new TextArea();
        a.setEditable(false);
        List<String> l = new ArrayList<String>();
        correspondingDecl.getRepresentation().accept(new DafnyTreeCallEntityVisitor(), l);
        vbox.getChildren().addAll(a);
        return vbox;
    }
}
