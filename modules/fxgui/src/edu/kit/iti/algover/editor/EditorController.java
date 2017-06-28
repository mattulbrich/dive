package edu.kit.iti.algover.editor;

import edu.kit.iti.algover.dafnystructures.DafnyFile;
import edu.kit.iti.algover.util.FileUtil;
import javafx.scene.control.Tab;
import javafx.scene.control.TabPane;
import org.fxmisc.richtext.CodeArea;

import java.io.BufferedReader;
import java.io.File;
import java.io.IOException;
import java.io.InputStreamReader;
import java.util.HashMap;
import java.util.Map;

/**
 * Created by philipp on 26.06.17.
 */
public class EditorController {

    private final File projectDirectory;
    private final TabPane view;
    private final Map<String, Tab> tabsByFile;

    public EditorController(File projectDirectory) {
        this.projectDirectory = projectDirectory;
        this.view = new TabPane();
        this.tabsByFile = new HashMap<>();
    }

    public void viewFile(String filename) {
        Tab existingTab = tabsByFile.get(filename);
        if (existingTab != null) {
            view.getSelectionModel().select(existingTab);
        } else {
            File file = new File(projectDirectory, filename);
            try (BufferedReader reader = new BufferedReader(new InputStreamReader(FileUtil.readFile(file)))) {
                StringBuilder builder = new StringBuilder();
                String line;
                while ((line = reader.readLine()) != null) {
                    builder.append(line);
                    builder.append('\n');
                }
                Tab tab = new Tab();
                tab.setText(filename);
                tab.setContent(new DafnyCodeArea(builder.toString()));
                tabsByFile.put(filename, tab);
                view.getTabs().add(tab);
                view.getSelectionModel().select(tab);
            } catch (IOException e) {
                e.printStackTrace();
            }
        }
    }

    public TabPane getView() {
        return view;
    }
}
