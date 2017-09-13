package edu.kit.iti.algover.editor;

import edu.kit.iti.algover.dafnystructures.DafnyFile;
import edu.kit.iti.algover.parser.DafnyTree;
import edu.kit.iti.algover.proof.PVC;
import edu.kit.iti.algover.references.CodeReference;
import edu.kit.iti.algover.symbex.AssertionElement;
import edu.kit.iti.algover.symbex.PathConditionElement;
import edu.kit.iti.algover.symbex.SymbexPath;
import edu.kit.iti.algover.util.ImmutableList;
import javafx.collections.ListChangeListener;
import javafx.scene.control.Tab;
import javafx.scene.control.TabPane;
import org.antlr.runtime.Token;
import org.fxmisc.richtext.CodeArea;

import java.io.IOException;
import java.nio.file.FileSystems;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.*;
import java.util.stream.Collectors;

/**
 * Created by philipp on 26.06.17.
 */
// TODO: Implement saving files / updating files when they change on disk
// but maybe that has to wait until ProjectManager is ready
public class EditorController {

    private static final int PVC_LAYER = 0;
    private static final int REFERENCE_LAYER = 1;

    private final TabPane view;
    private final Map<DafnyFile, Tab> tabsByFile;
    private final LayeredHighlightingRule highlightingLayers;

    public EditorController() {
        this.view = new TabPane();
        this.tabsByFile = new HashMap<>();
        this.highlightingLayers = new LayeredHighlightingRule(2);
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
                DafnyCodeArea codeArea = new DafnyCodeArea(contentAsText);
                codeArea.setHighlightingRule(highlightingLayers);
                tab.setContent(codeArea);
                tabsByFile.put(dafnyFile, tab);
                view.getTabs().add(tab);
                view.getSelectionModel().select(tab);
            } catch (IOException e) {
                e.printStackTrace();
            }
        }
    }

    private DafnyCodeArea getFocusedCodeArea() {
        return (DafnyCodeArea) view.getSelectionModel().getSelectedItem().getContent();
    }

    public void viewPVCSelection(PVC pvc) {
        highlightingLayers.setLayer(PVC_LAYER, new PVCHighlightingRule(pvc));

        view.getTabs().stream()
                .map(tab -> (DafnyCodeArea) tab.getContent())
                .forEach(DafnyCodeArea::rerenderHighlighting);
    }

    public void resetPVCSelection() {
        highlightingLayers.setLayer(PVC_LAYER, null);
        tabsByFile.forEach((key, value) -> {
            DafnyCodeArea codeArea = (DafnyCodeArea) value.getContent();
            codeArea.rerenderHighlighting();
        });
    }

    public TabPane getView() {
        return view;
    }

    private static String fileToString(String filename) throws IOException {
        Path path = FileSystems.getDefault().getPath(filename);
        return new String(Files.readAllBytes(path));
    }

    public void viewReferences(Set<CodeReference> codeReferences) {
        highlightingLayers.setLayer(REFERENCE_LAYER, new ReferenceHighlightingRule(codeReferences));

        view.getTabs().stream()
                .map(tab -> (DafnyCodeArea) tab.getContent())
                .forEach(DafnyCodeArea::rerenderHighlighting);
    }
}
