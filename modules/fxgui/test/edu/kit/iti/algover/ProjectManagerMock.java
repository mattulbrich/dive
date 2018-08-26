package edu.kit.iti.algover;

import edu.kit.iti.algover.project.ProjectManager;
import edu.kit.iti.algover.project.XMLProjectManager;

import java.io.File;

public class ProjectManagerMock {

    public static ProjectManager fromExample(String exampleName) {
        return fromProjectConfig(new File("doc/examples/" + exampleName), "config.xml");
    }

    public static ProjectManager fromProjectConfig(File dir, String configFile) {
        try {
            ProjectManager manager = new XMLProjectManager(dir, configFile);
            return manager;
        } catch (Exception e) {
            // REVIEW: Really only print and return null?
            e.printStackTrace();
        }

        return null;
    }
}
