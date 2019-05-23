/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 *  
 */

package edu.kit.iti.algover.swing;

import edu.kit.iti.algover.project.Project;

import javax.swing.*;
import java.awt.*;
import java.io.File;
import java.util.ArrayList;
import java.util.List;

public class DafnyCodeController {
    private DiveCenter diveCenter;

    private JTabbedPane tabs;
    private List<File> openFiles;

    public DafnyCodeController(DiveCenter diveCenter) {
        this.diveCenter = diveCenter;
        this.tabs = new JTabbedPane();
        this.openFiles = new ArrayList<>();

        diveCenter.project.addObserver(this::updateProject);
    }

    private void updateProject(Project project) {

        List<File> files = project.getConfiguration().getDafnyFiles();

        // close tabs
        for (File openFile : openFiles) {
            if(!files.contains(openFile)) {

            }
        }


    }

    public Component getComponent() {
        return tabs;
    }
}
