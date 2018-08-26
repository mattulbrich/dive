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
import edu.kit.iti.algover.parser.ReferenceResolutionVisitor;
import edu.kit.iti.algover.parser.TypeResolution;
import edu.kit.iti.algover.proof.PVC;
import edu.kit.iti.algover.proof.PVCGroup;
import edu.kit.iti.algover.proof.Proof;
import edu.kit.iti.algover.settings.ProjectSettings;
import edu.kit.iti.algover.util.FormatException;
import edu.kit.iti.algover.util.Util;
import org.xml.sax.SAXException;

import javax.xml.bind.JAXBException;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Date;
import java.util.HashMap;
import java.util.Map;
import java.util.Properties;

public class DafnyProjectManager extends AbstractProjectManager {

    private File masterFile;
    private File scriptFile;

    private Map<String, String> scriptDatabase;

    public DafnyProjectManager(File masterFile) throws FormatException, DafnyParserException, IOException, DafnyException {
        this.masterFile = masterFile;
        this.scriptFile = new File(masterFile.toString() + ".proofs");
        reload();
    }

    @Override
    public void reload() throws IOException, DafnyParserException {
        Project project = buildProject(masterFile);
        generateAllProofObjects(project);
        this.project.setValue(project);
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

        pb.getDafnyFiles().add(masterFile.toString());

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
        for (DafnyTree dafnyTree :
                masterAST.getChildrenWithType(DafnyParser.SETTINGS)) {
            System.out.println(dafnyTree.toStringTree());
        }
        pb.setSettings(settings);

        try {
            Project result = pb.build();
            return result;
        } catch (DafnyException ex) {
            throw new IOException(ex);
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
        Properties p = new Properties();
        if(scriptDatabase == null) {
            reloadScripts();
        }
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
        scriptDatabase.put(pvcIdentifier, proof.getScript());
    }

    @Override
    public String getName() {
        return masterFile.toString();
    }
}
