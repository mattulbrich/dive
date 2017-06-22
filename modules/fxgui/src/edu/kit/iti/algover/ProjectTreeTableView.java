package edu.kit.iti.algover;

import edu.kit.iti.algover.project.Project;
import javafx.beans.value.ObservableValue;
import javafx.scene.Node;
import javafx.scene.control.*;
import javafx.scene.paint.Color;

/**
 * Created by Philipp on 15.06.2017.
 */
public class ProjectTreeTableView extends TreeTableView<DafnyEntityModel> {

  private TreeTableColumn<DafnyEntityModel, String> nameColumn;
  private TreeTableColumn<DafnyEntityModel, Float> percentageProvenColumn;
  private TreeTableColumn<DafnyEntityModel, String> statusColumn;

  public ProjectTreeTableView(Project project) {
    this.nameColumn = new TreeTableColumn<>("name");
    this.percentageProvenColumn = new TreeTableColumn<>("percentage proven");
    this.statusColumn = new TreeTableColumn<>("status");

    super.setRoot(new DafnyEntityModel(project));

    nameColumn.setCellValueFactory(this::nameCellFactory);
    percentageProvenColumn.setCellValueFactory(this::percentageProvenCellFactory);
    statusColumn.setCellValueFactory(this::statusCellFactory);

    nameColumn.setCellFactory(this::nameCellRenderer);

    super.getColumns().setAll(nameColumn, percentageProvenColumn, statusColumn);
  }

  private TreeTableCell<DafnyEntityModel, String> nameCellRenderer(TreeTableColumn<DafnyEntityModel, String> column) {
    return new TreeTableCell<DafnyEntityModel, String>() {
      private DafnyEntityModel Dafny;

      public DafnyEntityModel getModel() {
        TreeTableRow<DafnyEntityModel> treeTableRow = getTreeTableRow();
        if (treeTableRow == null) return null;
        TreeItem<DafnyEntityModel> treeItem = treeTableRow.getTreeItem();
        if (treeItem == null) return null;
        return treeItem.getValue();
      }

      @Override
      protected void updateItem(String item, boolean empty) {
        super.updateItem(item, empty);
        DafnyEntityModel model = getModel();
        if (item != null && !empty && model != null) {
          setGraphic(graphicForKind(model.getKind()));
          setText(model.getName());
        }
      }
    };
  }

  private Node graphicForKind(DafnyEntityModel.Kind kind) {
    switch (kind) {
      case FUNCTION: return blueLabel("function");
      case CLASS: return blueLabel("class");
      case MODULE: return blueLabel("module");
      case METHOD: return blueLabel("method");
      default: return null;
    }
  }

  private Node blueLabel(String text) {
    Label label = new Label(text);
    label.setTextFill(Color.BLUE);
    return label;
  }

  private ObservableValue<String> nameCellFactory(TreeTableColumn.CellDataFeatures<DafnyEntityModel, String> data) {
    return data.getValue().getValue().nameProperty();
  }

  private ObservableValue<Float> percentageProvenCellFactory(TreeTableColumn.CellDataFeatures<DafnyEntityModel, Float> data) {
    return data.getValue().getValue().percentageProvenProperty().asObject();
  }

  private ObservableValue<String> statusCellFactory(TreeTableColumn.CellDataFeatures<DafnyEntityModel, String> data) {
    return data.getValue().getValue().statusProperty();
  }
}
