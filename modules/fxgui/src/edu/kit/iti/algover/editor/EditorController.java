package edu.kit.iti.algover.editor;

import edu.kit.iti.algover.dafnystructures.DafnyFile;
import edu.kit.iti.algover.proof.PVC;
import edu.kit.iti.algover.references.CodeReference;
import javafx.beans.property.BooleanProperty;
import javafx.beans.property.SimpleBooleanProperty;
import javafx.beans.value.ChangeListener;
import javafx.beans.value.ObservableValue;
import javafx.collections.ListChangeListener;
import javafx.scene.Node;
import javafx.scene.control.Tab;
import javafx.scene.control.TabPane;
import org.fxmisc.flowless.VirtualizedScrollPane;

import java.io.IOException;
import java.nio.file.FileSystems;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.HashMap;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.ExecutorService;

/**
 * Controller for the view that handles all {@link DafnyCodeArea} tabs.
 *
 * Created by philipp on 26.06.17.
 */
public class EditorController {

    private static final int PVC_LAYER = 0;
    private static final int REFERENCE_LAYER = 1;

    private final TabPane view;
    private final Map<DafnyFile, Tab> tabsByFile;
    private final LayeredHighlightingRule highlightingLayers;
    private final ExecutorService executor;

    private BooleanProperty anyFileChangedProperty;
    private int numFilesChanged = 0;

    /**
     * Initializes the controller without any code editor tabs.
     *
     * @param executor used by the code area components to asynchronously execute syntax highlighting calculations
     */
    public EditorController(ExecutorService executor) {
        this.executor = executor;
        this.view = new TabPane();
        this.tabsByFile = new HashMap<>();
        this.highlightingLayers = new LayeredHighlightingRule(2);
        this.anyFileChangedProperty = new SimpleBooleanProperty(false);
        view.getTabs().addListener(this::onTabListChanges);
    }

    private void onTabListChanges(ListChangeListener.Change<? extends Tab> change) {
        while (change.next()) {
            if (change.wasRemoved()) {
                for (Tab removedTab : change.getRemoved()) {
                    tabsByFile.remove(removedTab.getUserData());
                }
            }
        }
    }

    /**
     * If the Editor tab was already open, focus and show it, if not,
     * open a new tab that shows the given file.
     *
     * @param dafnyFile the file to be viewed to the user
     */
    public void viewFile(DafnyFile dafnyFile) {
        Tab existingTab = tabsByFile.get(dafnyFile);
        if (existingTab != null) {
            view.getSelectionModel().select(existingTab);
        } else {
            try {
                String contentAsText = fileToString(dafnyFile.getRepresentation().getFilename());
                Tab tab = new Tab();
                tab.setText(dafnyFile.getFilename());
                tab.setUserData(dafnyFile);
                DafnyCodeArea codeArea = new DafnyCodeArea(contentAsText, executor);
                codeArea.getTextChangedProperty().addListener(new ChangeListener<Boolean>() {
                    @Override
                    public void changed(ObservableValue<? extends Boolean> observable, Boolean oldValue, Boolean newValue) {
                        if(!oldValue && newValue) {
                            numFilesChanged++;
                        } else if(!newValue && oldValue) {
                            numFilesChanged--;
                        }
                        System.out.println(numFilesChanged);
                        if(numFilesChanged == 0) {
                            anyFileChangedProperty.setValue(false);
                        } else {
                            anyFileChangedProperty.setValue(true);
                        }
                        System.out.println(anyFileChangedProperty.get());
                    }
                });
                codeArea.setHighlightingRule(highlightingLayers);
                tab.setContent(new VirtualizedScrollPane<>(codeArea));
                tabsByFile.put(dafnyFile, tab);
                view.getTabs().add(tab);
                view.getSelectionModel().select(tab);
            } catch (IOException e) {
                e.printStackTrace();
            }
        }
    }

    private DafnyCodeArea getFocusedCodeArea() {
        return codeAreaFromContent(view.getSelectionModel().getSelectedItem().getContent());
    }

    /**
     * Highlight the symbolic execution path of given PVC using the {@link PVCHighlightingRule}.
     *
     * @param pvc the PVC to use for highlighting
     */
    public void viewPVCSelection(PVC pvc) {
        highlightingLayers.setLayer(PVC_LAYER, new PVCHighlightingRule(pvc));

        view.getTabs().stream()
                .map(tab -> codeAreaFromContent(tab.getContent()))
                .forEach(DafnyCodeArea::rerenderHighlighting);
    }

    /**
     * Resets any symbolic execution path in the editors. Only regular syntax or reference
     * highlighting will occur after this call.
     */
    public void resetPVCSelection() {
        highlightingLayers.setLayer(PVC_LAYER, null);
        tabsByFile.forEach((key, value) -> {
            DafnyCodeArea codeArea = codeAreaFromContent(value.getContent());
            codeArea.rerenderHighlighting();
        });
    }

    public TabPane getView() {
        return view;
    }

    private DafnyCodeArea codeAreaFromContent(Node content) {
        return ((VirtualizedScrollPane<DafnyCodeArea>) content).getContent();
    }

    private static String fileToString(String filename) throws IOException {
        Path path = FileSystems.getDefault().getPath(filename);
        return new String(Files.readAllBytes(path));
    }

    /**
     * Highlights all given {@link CodeReference}s using the {@link ReferenceHighlightingRule}.
     *
     * @param codeReferences code references to highlight
     */
    public void viewReferences(Set<CodeReference> codeReferences) {
        highlightingLayers.setLayer(REFERENCE_LAYER, new ReferenceHighlightingRule(codeReferences));

        view.getTabs().stream()
                .map(tab -> (DafnyCodeArea) tab.getContent())
                .forEach(DafnyCodeArea::rerenderHighlighting);
    }

    public BooleanProperty anyFileChangedProperty() {
        return anyFileChangedProperty;
    }

    public boolean getAnyFileChanged() {
        return anyFileChangedProperty.get();
    }

    public void setAnyFileChanged(boolean value) {
        anyFileChangedProperty.setValue(value);
    }
}
