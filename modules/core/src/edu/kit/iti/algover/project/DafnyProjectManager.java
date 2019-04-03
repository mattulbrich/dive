/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 *
 */

package edu.kit.iti.algover.project;

import edu.kit.iti.algover.parser.DafnyException;
import edu.kit.iti.algover.parser.DafnyFileParser;
import edu.kit.iti.algover.parser.DafnyParser;
import edu.kit.iti.algover.parser.DafnyParserException;
import edu.kit.iti.algover.parser.DafnyTree;
import edu.kit.iti.algover.proof.PVC;
import edu.kit.iti.algover.proof.Proof;
import edu.kit.iti.algover.settings.ProjectSettings;
import edu.kit.iti.algover.util.FormatException;
import edu.kit.iti.algover.util.Util;
import nonnull.NonNull;
import nonnull.Nullable;

import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.util.Date;
import java.util.HashMap;
import java.util.Map;
import java.util.Properties;
import java.util.logging.Logger;

/**
 * This project manager is a newer variant which does not use configuration
 * files but uses data which resides in .dfy files.
 *
 * It is parametrised by the main .dfy file.
 * That contains the "include" statements which defines the relevant source
 * files and contains "settings" paragraphs defining the settings.
 *
 * Proof scripts are stored in a xml-file whose name is the basename
 * concatenated with ".proofs".
 *
 * @author mulbrich
 */
public class DafnyProjectManager extends AbstractProjectManager {

    /**
     * The main file containing the includes and settings.
     */
    private final @NonNull File masterFile;

    /**
     * The file containing the scripts.
     *
     * essentially {@code = masterFile + ".proofs"}.
     */
    private final @NonNull File scriptFile;

    /**
     * The database of scripts as loaded from the scriptFile.
     * This is queried for lookups of scripts.
     * When reloading, the reference is reset to null.
     */
    private @Nullable Map<String, String> scriptDatabase;

    public DafnyProjectManager(@NonNull File masterFile) throws IOException, DafnyParserException {
        this.masterFile = masterFile;
        this.scriptFile = new File(masterFile.toString() + ".proofs");
        setProject(ProjectBuilder.emptyProject(masterFile.getParentFile()));
    }

    @Override
    public void reload() throws IOException, DafnyParserException {
        Project project = buildProject(masterFile);
        generateAllProofObjects(project);
        this.setProject(project);
    }

    /**
     * Generate all proof all available PVCs.
     *
     * Load and parse the script text if present.
     */
    private void generateAllProofObjects(Project project) throws IOException {
        proofs = new HashMap<>();

        if(scriptDatabase == null) {
            reloadScripts();
        }

        for (PVC pvc : project.getPVCByNameMap().values()) {
            Proof p = new Proof(project, pvc);
            String script;
            try {
                script = loadScriptForPVC(pvc.getIdentifier());
            } catch(FileNotFoundException ex) {
                script = project.getSettings().getString(ProjectSettings.DEFAULT_SCRIPT);
            }
            p.setScriptText(script);

            proofs.put(pvc.getIdentifier(), p);
        }
    }

    private static Project buildProject(File masterFile) throws IOException, DafnyParserException {

        ProjectBuilder pb = new ProjectBuilder();
        File dir = masterFile.getAbsoluteFile().getParentFile();
        pb.setDir(dir);

        DafnyTree masterAST = DafnyFileParser.parse(masterFile);

        pb.getDafnyFiles().add(masterFile.getName());

        for (DafnyTree include :
                masterAST.getChildrenWithType(DafnyParser.INCLUDE)) {
            DafnyTree fileNameAST = include.getFirstChildWithType(DafnyParser.STRING_LIT);
            String fileName = Util.stripQuotes(fileNameAST.token.getText());
            if (include.getFirstChildWithType(DafnyParser.FREE) != null) {
                pb.getLibraryFiles().add(new File(dir, fileName).toString());
            } else {
                pb.getDafnyFiles().add(new File(dir, fileName).toString());
            }
        }

        Map<String, String> settings = new HashMap<>();
        for (DafnyTree settingsTree :
                masterAST.getChildrenWithType(DafnyParser.SETTINGS)) {
            for (DafnyTree keyValuePair : settingsTree.getChildren()) {
                String key = Util.stripQuotes(keyValuePair.getText());
                String value = Util.stripQuotes(keyValuePair.getChild(0).getText());
                settings.put(key, value);
            }
        }

        pb.setSettings(settings);

        try {
            Project result = pb.build();
            return result;
        } catch (DafnyException ex) {
            throw new IOException(ex.getMessage(), ex);
        }
    }

    private void reloadScripts() throws IOException {
        Properties p = new Properties();
        try(FileInputStream in = new FileInputStream(scriptFile)) {
            p.loadFromXML(in);
            scriptDatabase = new HashMap<String, String>();
            p.forEach((k, v) -> scriptDatabase.put(k.toString(), v.toString()));
        } catch (FileNotFoundException databaseNotFound) {
            scriptDatabase = new HashMap<String, String>();
        }
    }

    @Override
    public String loadScriptForPVC(String pvc) throws IOException {
        if(scriptDatabase == null) {
            reloadScripts();
        }

        if (!scriptDatabase.containsKey(pvc)) {
            throw new FileNotFoundException(pvc + " not in DB");
        }
        return scriptDatabase.get(pvc);
    }

    @Override
    public void saveProject() throws IOException {
        super.saveProject();

        if (scriptDatabase == null) {
            // no scripts have been touched or changed
            return;
        }

        Properties p = new Properties();
        p.putAll(scriptDatabase);

        try(FileOutputStream fileOutputStream = new FileOutputStream(scriptFile)) {
            p.storeToXML(fileOutputStream,
                    "Created by Algover at " + new Date(),
                    "UTF8");
        }
    }

    @Override
    public void saveProofScriptForPVC(String pvcIdentifier, Proof proof) throws IOException {
        if(scriptDatabase == null) {
            reloadScripts();
        }
        System.out.println(proof.getScript());
        scriptDatabase.put(pvcIdentifier, proof.getScript());
    }

    @Override
    public String getName() {
        return masterFile.toString();
    }

    @Override
    public Configuration getConfiguration() {
        Configuration c =  getProject().getConfiguration();
        c.setBaseDir(getProject().getBaseDir());
        c.setMasterFile(this.masterFile);
        c.setSaveAsXML(false);
        return c;
    }

    @Override
    public void updateProject(Configuration config) throws IOException{
        try {
            DafnyProjectConfigurationChanger.saveConfiguration(config, config.getMasterFile());
        } catch (DafnyParserException e) {
            Logger.getGlobal().severe("Error while saving project settings to file: "+config.getMasterFile());
            e.printStackTrace();
        }
    }

    @Override
    public void saveProjectConfiguration() throws IOException {
        try {
            DafnyProjectConfigurationChanger.saveConfiguration(this.getConfiguration(), this.masterFile);
        } catch (DafnyParserException e) {
            Logger.getGlobal().warning("Error while saving configuration as Dafny master file "+this.masterFile);
            e.printStackTrace();
        }
    }
}
