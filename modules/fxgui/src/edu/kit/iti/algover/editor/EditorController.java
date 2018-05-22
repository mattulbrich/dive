package edu.kit.iti.algover.editor;

import edu.kit.iti.algover.dafnystructures.DafnyFile;
import edu.kit.iti.algover.project.Project;
import edu.kit.iti.algover.proof.PVC;
import edu.kit.iti.algover.references.CodeReference;
import javafx.beans.property.BooleanProperty;
import javafx.beans.property.SimpleBooleanProperty;
import javafx.beans.value.ChangeListener;
import javafx.beans.value.ObservableValue;
import javafx.collections.ListChangeListener;
import javafx.scene.Node;
import javafx.scene.control.Alert;
import javafx.scene.control.ButtonType;
import javafx.scene.control.Tab;
import javafx.scene.control.TabPane;
import javafx.scene.input.KeyCode;
import javafx.scene.input.KeyCodeCombination;
import javafx.scene.input.KeyCombination;
import javafx.scene.input.KeyEvent;
import org.fxmisc.flowless.VirtualizedScrollPane;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.nio.file.FileSystems;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.*;
import java.util.concurrent.ExecutorService;
import java.util.logging.Logger;

/**
 * Controller for the view that handles all {@link DafnyCodeArea} tabs.
 *
 * Created by philipp on 26.06.17.
 */
public class EditorController implements DafnyCodeAreaListener {
    KeyCombination saveShortcut = new KeyCodeCombination(KeyCode.S, KeyCombination.CONTROL_DOWN);
    KeyCombination saveAllShortcut = new KeyCodeCombination(KeyCode.S, KeyCombination.CONTROL_DOWN, KeyCombination.SHIFT_DOWN);

    private static final int PVC_LAYER = 0;
    private static final int REFERENCE_LAYER = 1;

    private final TabPane view;
    //Maps the filename to the tab this file is open in.
    //TODO the filename seems not to be optimal since theoretically there may be several files with the same name
    //TODO but the DafnyFile is not suitable since it may change on reloads
    private final Map<String, Tab> tabsByFile;
    private final LayeredHighlightingRule highlightingLayers;
    private final ExecutorService executor;

    private BooleanProperty anyFileChangedProperty;
    private List<String> changedFiles;
    private String baseDir;

    /**
     * Initializes the controller without any code editor tabs.
     *
     * @param executor used by the code area components to asynchronously execute syntax highlighting calculations
     */
    public EditorController(ExecutorService executor, String baseDir) {
        this.executor = executor;
        this.baseDir = baseDir;
        this.view = new TabPane();
        this.tabsByFile = new HashMap<>();
        this.changedFiles = new ArrayList<>();
        this.highlightingLayers = new LayeredHighlightingRule(2);
        this.anyFileChangedProperty = new SimpleBooleanProperty(false);
        view.getTabs().addListener(this::onTabListChanges);
        view.setOnKeyReleased(this::handleShortcuts);
    }

    private void handleShortcuts(KeyEvent keyEvent) {
        if(saveAllShortcut.match(keyEvent)) {
            saveAllFiles();
        } else if (saveShortcut.match(keyEvent)) {
            saveSelectedFile();
        }
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
        Tab existingTab = tabsByFile.get(dafnyFile.getFilename());
        if (existingTab != null) {
            view.getSelectionModel().select(existingTab);
        } else {
            try {
                String contentAsText = fileToString(dafnyFile.getRepresentation().getFilename());
                Tab tab = new Tab();
                tab.setText(dafnyFile.getFilename());
                tab.setUserData(dafnyFile);
                DafnyCodeArea codeArea = new DafnyCodeArea(contentAsText, executor, this);
                codeArea.getTextChangedProperty().addListener(this::onTextChanged);
                codeArea.setHighlightingRule(highlightingLayers);
                tab.setContent(new VirtualizedScrollPane<>(codeArea));
                tabsByFile.put(dafnyFile.getFilename(), tab);
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

    private void onTextChanged(ObservableValue<? extends Boolean> observable, Boolean oldValue, Boolean newValue) {
        Tab selectedTab = view.getSelectionModel().getSelectedItem();
        if(!changedFiles.contains(selectedTab.getText()) && newValue) {
            selectedTab.setText(selectedTab.getText() + "*");
            changedFiles.add(selectedTab.getText());
        } else if(changedFiles.contains(selectedTab.getText()) && !newValue) {
            changedFiles.remove(selectedTab.getText());
            selectedTab.setText(selectedTab.getText().substring(0, selectedTab.getText().length() - 1));
        }
        if(changedFiles.size() == 0) {
            anyFileChangedProperty.setValue(false);
        } else {
            anyFileChangedProperty.setValue(true);
        }
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

    private boolean getAnyFileChanged() {
        return anyFileChangedProperty.get();
    }

    private void setAnyFileChanged(boolean value) {
        anyFileChangedProperty.setValue(value);
    }

    @Override
    public void saveSelectedFile() {
        Tab selectedTab = view.getSelectionModel().getSelectedItem();
        saveFileForTab(selectedTab);
    }

    @Override
    public void saveAllFiles() {
        view.getTabs().stream().forEach(tab -> saveFileForTab(tab));
    }

    private void saveFileForTab(Tab tab) {
        if(tab.getUserData() instanceof  DafnyFile) {
            String filename = ((DafnyFile) tab.getUserData()).getFilename();
            String absFilepath = baseDir + "/" + filename;
            try {
                FileWriter fw = new FileWriter(absFilepath);
                BufferedWriter bw = new BufferedWriter(fw);
                DafnyCodeArea codeArea = codeAreaFromContent(tab.getContent());
                bw.write(codeArea.getText());
                bw.flush();
                bw.close();
                fw.close();
                changedFiles.remove(tab.getText());
                codeArea.updateProofText();
                if(tab.getText().endsWith("*")) {
                    tab.setText(tab.getText().substring(0, tab.getText().length() - 1));
                }
                if(changedFiles.size() == 0) {
                    anyFileChangedProperty().setValue(false);
                }
                Logger.getLogger(Logger.GLOBAL_LOGGER_NAME).info("Successfully saved file " + filename + ".");
            } catch(IOException e) {
                Logger.getLogger(Logger.GLOBAL_LOGGER_NAME).severe("Error saving file" + filename + ".");
            }
        }
    }
}
