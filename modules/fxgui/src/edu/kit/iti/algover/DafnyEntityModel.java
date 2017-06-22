package edu.kit.iti.algover;

import edu.kit.iti.algover.dafnystructures.DafnyClass;
import edu.kit.iti.algover.dafnystructures.DafnyFile;
import edu.kit.iti.algover.dafnystructures.DafnyMethod;
import edu.kit.iti.algover.project.Project;
import javafx.beans.property.FloatProperty;
import javafx.beans.property.SimpleFloatProperty;
import javafx.beans.property.SimpleStringProperty;
import javafx.beans.property.StringProperty;
import javafx.scene.control.TreeItem;

import java.util.Collection;
import java.util.Collections;
import java.util.stream.Collectors;

/**
 * Created by Philipp on 16.06.2017.
 */
public class DafnyEntityModel extends TreeItem<DafnyEntityModel> {

  public Kind getKind() {
    return kind;
  }

  public enum Kind {
    METHOD,
    FUNCTION,
    CLASS,
    MODULE,
    OTHER // Does not render specially. E.g. the root node or file nodes
  }

  public static final String PROVEN = "Proven";
  public static final String UNPROVEN = "Unproven";

  private StringProperty name;
  private FloatProperty percentageProven;
  private StringProperty status;
  private final Kind kind;

  private static DafnyEntityModel entityFromFile(DafnyFile dafnyFile) {
    Collection<DafnyEntityModel> methods =
        dafnyFile.getMethods().stream()
        .map(DafnyEntityModel::entityFromMethod)
        .collect(Collectors.toList());
    Collection<DafnyEntityModel> children =
        dafnyFile.getClasses().stream()
        .map(DafnyEntityModel::entityFromClass)
        .collect(Collectors.toList());
    children.addAll(methods);
    return new DafnyEntityModel(Kind.OTHER, dafnyFile.getName(), 0, UNPROVEN, children);
  }

  private static DafnyEntityModel entityFromClass(DafnyClass dafnyClass) {
    Collection<DafnyEntityModel> children =
        dafnyClass.getMethods().stream()
            .map(DafnyEntityModel::entityFromMethod)
            .collect(Collectors.toList());
    return new DafnyEntityModel(Kind.CLASS, dafnyClass.getName(), 0, UNPROVEN, children);
  }

  private static DafnyEntityModel entityFromMethod(DafnyMethod dafnyMethod) {
    return new DafnyEntityModel(Kind.METHOD, dafnyMethod.getName(), 0, UNPROVEN, Collections.emptyList());
  }

  // TODO: Modules and Functions

  public DafnyEntityModel(Project project) {
    this(Kind.OTHER, "Dafny Files", 0, UNPROVEN, Collections.emptyList());
    getChildren().setAll(
        project.getDafnyFiles().stream()
            .map(DafnyEntityModel::entityFromFile)
            .collect(Collectors.toList()));
  }

  public DafnyEntityModel(Kind kind, String name, float percentageProven, String status, Collection<DafnyEntityModel> children) {
    this.kind = kind;
    this.name = new SimpleStringProperty(name);
    this.percentageProven = new SimpleFloatProperty(percentageProven);
    this.status = new SimpleStringProperty(status);
    getChildren().setAll(children);
    setValue(this);
  }

  public String getName() {
    return name.get();
  }

  public StringProperty nameProperty() {
    return name;
  }

  public float getPercentageProven() {
    return percentageProven.get();
  }

  public FloatProperty percentageProvenProperty() {
    return percentageProven;
  }

  public String getStatus() {
    return status.get();
  }

  public StringProperty statusProperty() {
    return status;
  }

}
