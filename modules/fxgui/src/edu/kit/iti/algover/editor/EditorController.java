package edu.kit.iti.algover.editor;

import edu.kit.iti.algover.dafnystructures.DafnyFile;
import edu.kit.iti.algover.parser.DafnyTree;
import edu.kit.iti.algover.proof.PVC;
import edu.kit.iti.algover.symbex.AssertionElement;
import edu.kit.iti.algover.symbex.PathConditionElement;
import edu.kit.iti.algover.symbex.SymbexPath;
import edu.kit.iti.algover.util.ImmutableList;
import javafx.collections.ListChangeListener;
import javafx.scene.control.Tab;
import javafx.scene.control.TabPane;
import org.antlr.runtime.Token;

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

    private final TabPane view;
    private final Map<DafnyFile, Tab> tabsByFile;

    public EditorController() {
        this.view = new TabPane();
        this.tabsByFile = new HashMap<>();
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
                tab.setContent(new DafnyCodeArea(contentAsText));
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
        DafnyCodeArea codeArea = getFocusedCodeArea();
        codeArea.setHighlightingRule(new PVCHighlightingRule(pvc));
        codeArea.rerenderHighlighting();
    }

    public void resetPVCSelection() {
        DafnyCodeArea codeArea = getFocusedCodeArea();
        codeArea.setHighlightingRule(null);
        codeArea.rerenderHighlighting();
    }

    public TabPane getView() {
        return view;
    }

    private static String fileToString(String filename) throws IOException {
        Path path = FileSystems.getDefault().getPath(filename);
        return new String(Files.readAllBytes(path));
    }
}
