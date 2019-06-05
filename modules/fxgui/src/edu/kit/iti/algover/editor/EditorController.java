package edu.kit.iti.algover.editor;

import edu.kit.iti.algover.Lookup;
import edu.kit.iti.algover.MainController;
import edu.kit.iti.algover.dafnystructures.DafnyFile;
import edu.kit.iti.algover.proof.PVC;
import edu.kit.iti.algover.referenceHighlighting.ReferenceHighlightingHandler;
import edu.kit.iti.algover.referenceHighlighting.ReferenceHighlightingObject;
import edu.kit.iti.algover.references.CodeReferenceTarget;
import edu.kit.iti.algover.util.ExceptionDetails;
import javafx.beans.property.BooleanProperty;
import javafx.beans.property.SimpleBooleanProperty;
import javafx.beans.value.ObservableValue;
import javafx.collections.ListChangeListener;
import javafx.collections.ObservableList;
import javafx.event.Event;
import javafx.event.EventHandler;
import javafx.scene.Node;
import javafx.scene.control.Tab;
import javafx.scene.control.TabPane;
import javafx.scene.control.Tooltip;
import javafx.scene.input.KeyCode;
import javafx.scene.input.KeyCodeCombination;
import javafx.scene.input.KeyCombination;
import javafx.scene.input.KeyEvent;
import org.antlr.runtime.Token;
import org.controlsfx.dialog.ExceptionDialog;
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
 * <p>
 * Created by philipp on 26.06.17.
 */
public class EditorController implements DafnyCodeAreaListener, ReferenceHighlightingHandler {
    KeyCombination saveShortcut = new KeyCodeCombination(KeyCode.S, KeyCombination.CONTROL_DOWN);
    KeyCombination saveAllShortcut = new KeyCodeCombination(KeyCode.S, KeyCombination.CONTROL_DOWN, KeyCombination.SHIFT_DOWN);

    private static final int PVC_LAYER = 0;
    private static final int REFERENCE_LAYER = 1;

    private static final int ERROR_LAYER = 2;


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
    private Set<CodeReferenceTarget> codeReferenceTargets = new HashSet<>();

    private String recentSelectedTab;

    /**
     * Initializes the controller without any code editor tabs.
     *
     * @param executor used by the code area components to asynchronously execute syntax highlighting calculations
     */
    public EditorController(ExecutorService executor, String baseDir, Lookup lookup) {
        this.executor = executor;
        this.baseDir = baseDir;
        this.view = new TabPane();
        this.tabsByFile = new HashMap<>();
        this.changedFiles = new ArrayList<>();
        this.highlightingLayers = new LayeredHighlightingRule(3);
        this.anyFileChangedProperty = new SimpleBooleanProperty(false);
        view.getTabs().addListener(this::onTabListChanges);
        view.setOnKeyReleased(this::handleShortcuts);
        lookup.register(this, ReferenceHighlightingHandler.class);
        lookup.register(this, EditorController.class);
    }

    private void handleShortcuts(KeyEvent keyEvent) {
        if (saveAllShortcut.match(keyEvent)) {
            saveAllFiles();
        } else if (saveShortcut.match(keyEvent)) {
            saveSelectedFile();
        }
    }

    private void onTabListChanges(ListChangeListener.Change<? extends Tab> change) {
        while (change.next()) {
            if (change.wasRemoved()) {
                for (Tab removedTab : change.getRemoved()) {
                    String f = (String) (removedTab.getUserData());
                    tabsByFile.remove(f);
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
        viewFile(dafnyFile.getFilename());
    }

    public void viewFile(String fileName) {
        Tab existingTab = tabsByFile.get(fileName);
        if (existingTab != null) {
            view.getSelectionModel().select(existingTab);
        } else {
            try {
                String contentAsText = fileToString(fileName);
                Tab tab = new Tab();
                File file = new File(fileName);
                tab.setText(file.getName());
                tab.setTooltip(new Tooltip(file.getAbsolutePath()));
                tab.setUserData(fileName);
                DafnyCodeArea codeArea = new DafnyCodeArea(contentAsText, executor, this);
                codeArea.setHighlightingRule(highlightingLayers);
                tab.setContent(new VirtualizedScrollPane<>(codeArea));
                tabsByFile.put(fileName, tab);
                view.getTabs().add(tab);
                view.getSelectionModel().select(tab);
                codeArea.getTextChangedProperty().addListener(this::onTextChanged);
            } catch (IOException e) {
                e.printStackTrace();
                ExceptionDialog exdlg = new ExceptionDialog(e);
                exdlg.showAndWait();
            }
        }
    }

    private DafnyCodeArea getFocusedCodeArea() {
        Tab selectedItem = view.getSelectionModel().getSelectedItem();
        if (selectedItem != null) {
            return codeAreaFromContent(selectedItem.getContent());
        } else {
            return null;
        }
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

    public void showException(Throwable exception) {
        ExceptionDetails.ExceptionReportInfo ri = ExceptionDetails.extractReportInfo(exception);
        int line = ri.getLine();
        int col = ri.getColumn() - 1;
        int endCol = col + ri.getLength();
        String filename = ri.getFilename();

        if(filename == null) {
            return;
        }

        highlightingLayers.setLayer(ERROR_LAYER, new HighlightingRule() {
            @Override
            public Collection<String> handleToken(Token token, Collection<String> syntaxClasses) {
                int tokenLine = token.getLine();
                int tokenCol = token.getCharPositionInLine();
                if (tokenLine == line && col <= tokenCol && tokenCol < endCol) {
                    return Collections.singleton("error");
                }
                return syntaxClasses;
            }
        });

        viewFile(filename);
        assert getFocusedCodeArea() != null;
        getFocusedCodeArea().rerenderHighlighting();
    }

    public void resetExceptionLayer() {
        highlightingLayers.setLayer(ERROR_LAYER, new HighlightingRule() {
            @Override
            public Collection<String> handleToken(Token token, Collection<String> syntaxClasses) {
                return syntaxClasses;
            }
        });
    }

    private void onTextChanged(ObservableValue<? extends Boolean> observable, Boolean oldValue, Boolean newValue) {
        Tab selectedTab = view.getSelectionModel().getSelectedItem();
        if (!changedFiles.contains(selectedTab.getText()) && newValue) {
            selectedTab.setText(selectedTab.getText() + "*");
            changedFiles.add(selectedTab.getText());
        } else if (changedFiles.contains(selectedTab.getText()) && !newValue) {
            changedFiles.remove(selectedTab.getText());
            selectedTab.setText(selectedTab.getText().substring(0, selectedTab.getText().length() - 1));
        }
        if (changedFiles.size() == 0) {
            anyFileChangedProperty.setValue(false);
        } else {
            anyFileChangedProperty.setValue(true);
        }
        resetExceptionLayer();
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

    @SuppressWarnings("unchecked")
    private DafnyCodeArea codeAreaFromContent(Node content) {
        return ((VirtualizedScrollPane<DafnyCodeArea>) content).getContent();
    }

    private static String fileToString(String filename) throws IOException {
        Path path = FileSystems.getDefault().getPath(filename);
        return new String(Files.readAllBytes(path));
    }

    /**
     * Highlights all given {@link CodeReferenceTarget}s using the {@link ReferenceHighlightingRule}.
     *
     * @param codeReferenceTargets code references to highlight
     */
    public void viewReferences(Set<CodeReferenceTarget> codeReferenceTargets) {
        this.codeReferenceTargets = codeReferenceTargets;
        highlightingLayers.setLayer(REFERENCE_LAYER, new ReferenceHighlightingRule(codeReferenceTargets));
        view.getTabs().stream()
                .map(tab -> codeAreaFromContent(tab.getContent()))
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
        assert tab.getUserData() instanceof String : "Expecting filename in user data";
        String filename = tab.getUserData().toString();
        File absFile = new File(filename);
        if (!absFile.isAbsolute()) {
            absFile = new File(baseDir, filename);
        }
        try(BufferedWriter bw = new BufferedWriter(new FileWriter(absFile))) {
            DafnyCodeArea codeArea = codeAreaFromContent(tab.getContent());
            bw.write(codeArea.getText());
            bw.flush();
            changedFiles.remove(tab.getText());
            codeArea.updateProofText();
            if (tab.getText().endsWith("*")) {
                tab.setText(tab.getText().substring(0, tab.getText().length() - 1));
            }
            if (changedFiles.size() == 0) {
                anyFileChangedProperty().setValue(false);
            }
            Logger.getLogger(Logger.GLOBAL_LOGGER_NAME).info("Successfully saved file " + filename + ".");
        } catch (IOException e) {
            Logger.getLogger(Logger.GLOBAL_LOGGER_NAME).severe("Error saving file" + filename + ".");
        }
    }

    @Override
    public void handleReferenceHighlighting(ReferenceHighlightingObject references) {
        viewReferences(references.getCodeReferenceTargetSet());
    }

    @Override
    public void removeReferenceHighlighting() {

        highlightingLayers.setLayer(REFERENCE_LAYER, new ReferenceHighlightingRule(new HashSet<>()));
        view.getTabs().stream()
                .map(tab -> codeAreaFromContent(tab.getContent()))
                .forEach(DafnyCodeArea::rerenderHighlighting);
    }
    private List<String> saveOrderOfOpenTabsByFilename(ObservableList<Tab> tabsInView){

        Set<String> filenamesSet = new HashSet<>(tabsByFile.keySet());
        ArrayList<String> filenames = new ArrayList<>();
        Iterator<Tab> iteratorTabsInView = tabsInView.iterator();
        Tab tabInView;
        String name;
        //copy the order of the current open tabs from the view and add the filenames into the temporary list being able to restore the order
        while(iteratorTabsInView.hasNext()){
            tabInView = iteratorTabsInView.next();
            name = (String) tabInView.getUserData();
            if(filenamesSet.contains(name)){
                filenames.add(name);
                filenamesSet.remove(name);
            } else {
                throw new RuntimeException("Was not able to reconstruct interface, please restart DIVE");
            }

        }
        assert filenamesSet.isEmpty();
        return filenames;
    }

    /**
     * Reload all open tabs by keeping the order of previous opened tabs
     */
    public void reloadAllOpenFiles() {
        saveRecentSelectedTab();
        ObservableList<Tab> tabsInView = getView().getTabs();
        List<String> filenames = saveOrderOfOpenTabsByFilename(tabsInView);

        Collection<Tab> tabs = new ArrayList<>(tabsByFile.values());
        //close all tabs and remove them from the view
        removeTabsInView(tabsInView, tabs);
        //iterate through the list of files and open files again
        filenames.forEach(s -> viewFile(s));
        selectRecentTab();
    }

    private void removeTabsInView(ObservableList<Tab> tabsInView, Collection<Tab> tabstoClose) {
        for (Tab tab : tabstoClose) {
            tabsInView.remove(tab);
        }
    }

    /**
     * If a tab was selected, save this selction to a member variable
     */
    public void saveRecentSelectedTab(){
        Tab userData = getView().getSelectionModel().getSelectedItem();
        if(userData != null) {
            this.recentSelectedTab = (String) userData.getUserData();
        }

    }

    /**
     * Select the tab that is stored by calling saveRecentSelectedTab
     */
    public void selectRecentTab(){
        getView().getSelectionModel().select(tabsByFile.get(recentSelectedTab));
    }

    /**
     * Refresh the current tab view by first saving the order of the last opened tabs, then opening only those tabs that
     * are passed in the list of dafnyfiles trying to restore the order
     * @param dafnyFiles
     */
    public void refreshTabView(List<DafnyFile> dafnyFiles) {
        saveRecentSelectedTab();
        List<String> passedDfyFiles = new ArrayList<String>();
        dafnyFiles.forEach(file -> passedDfyFiles.add(file.getName()));
        ObservableList<Tab> tabsOpenInView = getView().getTabs();

        List<String> lastOpenedFiles = saveOrderOfOpenTabsByFilename(tabsOpenInView);

        Collection<Tab> values = new HashSet<>(tabsByFile.values());
        removeTabsInView(tabsOpenInView, values);

        Iterator<String> iterator = lastOpenedFiles.iterator();
        while(iterator.hasNext()){
            String next = iterator.next();
            if(passedDfyFiles.contains(next)){
                viewFile(next);
                passedDfyFiles.remove(next);
            }
        }
        if(!passedDfyFiles.isEmpty()){
            passedDfyFiles.forEach(file -> viewFile(file));
        }

        if(tabsByFile.containsKey(this.recentSelectedTab)){
            selectRecentTab();
        }


    }
}
