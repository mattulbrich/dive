package edu.kit.iti.algover;

import edu.kit.iti.algover.project.ProjectManager;

import java.io.File;

public class ProjectManagerMock {

    public static ProjectManager fromExample(String exampleName) {
        return fromProjectConfig(new File("doc/examples/" + exampleName + "/config.xml"));
    }

    public static ProjectManager fromProjectConfig(File configFile) {
        ProjectManager manager = new ProjectManager();
        try {
            manager.loadProject(configFile);
        } catch (Exception e) {
            e.printStackTrace();
        }
        return manager;
    }
}
