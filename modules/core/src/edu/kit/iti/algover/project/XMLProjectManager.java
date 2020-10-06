/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.project;

import edu.kit.iti.algover.dafnystructures.DafnyFile;
import edu.kit.iti.algover.parser.DafnyException;
import edu.kit.iti.algover.parser.DafnyParserException;
import edu.kit.iti.algover.proof.PVC;
import edu.kit.iti.algover.proof.Proof;
import edu.kit.iti.algover.settings.ProjectSettings;
import edu.kit.iti.algover.util.FormatException;
import edu.kit.iti.algover.util.Util;
import org.xml.sax.SAXException;

import javax.xml.bind.JAXBException;
import java.io.*;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.logging.Logger;
import java.util.stream.Collectors;

/**
 * A project manager that receives a directory and a config.xml file for
 * configuration.
 *
 * Scripts are stored in individual files in a subdirectory "scripts".
 *
 * @author Sarah Grebing
 * @author Mattias Ulbrich, refactored Jan 2018
 */
public final class XMLProjectManager extends AbstractProjectManager {

    private static final String CONFIG_DEFAULT_NAME = ProjectBuilder.CONFIG_DEFAULT_FILENAME;

    /**
     * the name of the config.xml file within the directory.
     */
    private final String configFilename;

    /**
     * the directory in which the project resides.
     */
    private final File directory;

    /**
     * Build a new project by parsing the config file and performing symbolic execution
     *
     * @param directory      the directory where the problem resides in
     * @param configFilename the filename of the configuration within this directory
     * @throws DafnyException       if name/type resolution fails
     * @throws DafnyParserException if dafny parsing fails
     * @throws IOException          if XML is wrongly formatted or files cannot be read
     * @throws FormatException      if the settings in the config file are illegally formatted.
     */
    public XMLProjectManager(File directory, String configFilename) throws FormatException, IOException {
        this.directory = directory;
        this.configFilename = configFilename;
        this.setProject(buildEmptyProject(directory, configFilename));
    }

    /**
     * Reload the project.
     *
     * <P>Reparse the source code and the config files and. Regenerate the proof objects throwing away existing
     * objects.
     *
     * @throws DafnyException       if name/type resolution fails
     * @throws DafnyParserException if dafny parsing fails
     * @throws IOException          if XML is wrongly formatted or files cannot be read
     * @throws FormatException      if the settings in the config file are illegally formatted.
     */
    @Override
    public void reload() throws DafnyException, DafnyParserException, IOException, FormatException {
        Project project = buildProject(directory, configFilename);
        generateAllProofObjects(project);
        this.setProject(project);
    }

    /**
     * Build a new Project by parsing the config file and performing symbolic execution
     *
     * @param path           the directory where the problem resides in
     * @param configFilename the filename of the configuration within this directory
     * @return a freshly created project read from the directory and configFilename
     * @throws DafnyException       if name/type resolution fails
     * @throws DafnyParserException if dafny parsing fails
     * @throws IOException          if XML is wrongly formatted or files cannot be read
     * @throws FormatException      if the settings in the config file are illegally formatted.
     */
    private static Project buildProject(File path, String configFilename)
            throws DafnyException, DafnyParserException, IOException, FormatException {
        ProjectBuilder pb = new ProjectBuilder();
        pb.setDir(path);
        try {
            parseProjectConfigurationFile(path, configFilename, pb);
            pb.validateProjectConfiguration();
        } catch (JAXBException|SAXException e) {
            // subsume the XML exceptions under IOException.
            throw new IOException(e);
        }

        Project result = pb.build();

        return result;
    }

    /**
     * This method loads the configuration file, extracts all entities and sets
     * member variables accordingly.
     *
     * Moved from class {@link ProjectBuilder}, since it makes sense only
     * for XML projects.
     *
     * It is public for access of legacy test cases.
     */
    public static void parseProjectConfigurationFile(File path, String configFilename, ProjectBuilder pb) throws JAXBException, SAXException {

        File configFile = new File(path, configFilename);

        Configuration config = ConfigXMLLoader.loadConfigFile(configFile);

        if (config.getDafnyFiles() != null) {
            config.getDafnyFiles().stream().forEach(file -> {
                pb.addInputFile(file.getPath());
            });
        }
        if (config.getLibFiles() != null) {
            config.getLibFiles().stream().forEach(file -> {
                pb.addLibraryFile(file.getPath());
            });
        }

        Map<String, String> settings = config.getSettings();
        if(settings != null) {
            pb.setSettings(settings);
        }
    }

    private Project buildEmptyProject(File path, String configFilename)
            throws IOException, FormatException {
        return ProjectBuilder.emptyProject(path);
    }

    /**
     * Generate all proof all available PVCs.
     *
     * Load and parse the script text if present.
     */
    private void generateAllProofObjects(Project project) throws IOException {
        proofs = new HashMap<>();
        for (PVC pvc : project.getPVCByNameMap().values()) {
            List<DafnyFile> dfyFiles = project.getDafnyFiles().stream()
                    .filter(dafnyFile -> dafnyFile.getFilename().equals(pvc.getDeclaration().getFilename()))
                    .collect(Collectors.toList());

            assert dfyFiles.size() <= 1;

            if(dfyFiles.isEmpty()) {
                throw new IOException("Could not find Dafny file for pvc: " + pvc.toString());
            }

            Proof p = new Proof(project, pvc);
            for (DafnyFile dfyFile : dfyFiles) {
                p.getReferenceGraph().addFromReferenceMap(dfyFile, pvc.getReferenceMap());
            }
            String script;
            try {
                script = loadScriptForPVC(pvc.getIdentifier());
            } catch (FileNotFoundException ex) {
                script = project.getSettings().getString(ProjectSettings.DEFAULT_SCRIPT_PROP.key);
            }

            p.setScriptText(script);

            proofs.put(pvc.getIdentifier(), p);
        }
    }

    @Override
    public String loadScriptForPVC(String pvc) throws IOException {
        // find file on disc
        File scriptFile = getScriptFileForPVC(pvc);

        if(!scriptFile.exists()) {
            throw new FileNotFoundException(scriptFile.getAbsolutePath());
        }

        return new String(Files.readAllBytes(scriptFile.toPath()));
    }

    private File getScriptFileForPVC(String pvcIdentifier) {
        File proofDir = new File(directory, "scripts");
        return new File(proofDir, Util.maskFileName(pvcIdentifier) + ".script");
    }


    @Override
    public void saveProofScriptForPVC(String pvcIdentifier, Proof proof) throws IOException {
        File scriptFile = getScriptFileForPVC(pvcIdentifier);
        saverHelper(scriptFile.getPath(), proof.getScriptText());
    }

    private void saverHelper(String pathToFile, String content) throws IOException {
        Path path = Paths.get(pathToFile);
        Writer writer;
        if (Files.exists(path)) {
            writer = Files.newBufferedWriter(path);
        } else {
            Files.createDirectories(path.getParent());
            Path file = Files.createFile(path);
            writer = Files.newBufferedWriter(file);
        }
        writer.write(content);
        writer.flush();
        writer.close();
    }

    @Override
    public String getName() {
        return directory.getName();
    }

    @Override
    public Configuration getConfiguration() {
        Configuration configuration = getProject().getConfiguration();
        configuration.setBaseDir(getProject().getBaseDir());
        configuration.setConfigFile(this.configFilename);
        configuration.setSaveAsXML(true);
        return configuration;
    }

    @Override
    public void updateProject(Configuration config) throws IOException, DafnyParserException, FormatException, DafnyException {
        saveConfiguration(config);
        this.reload();
    }

    @Override
    public void saveProjectConfiguration() throws IOException {
        saveConfiguration(this.getConfiguration());
    }

    public String getConfigFilename() {
        return configFilename;
    }

    public File getDirectory() {
        return directory;
    }


    /**
     * Write a configuration to the XML file specified in the configuration object
     * @param config
     */
    public static void saveConfiguration(Configuration config) throws IOException {
        File baseDir = config.getBaseDir();
        String configFile = config.getConfigFile();
        try {

            Path configXML = Paths.get(baseDir + File.separator + configFile);
            if (baseDir.exists() && configFile.endsWith(".xml")) {
                Path file;
                if(!configXML.toFile().exists()) {
                    file = Files.createFile(configXML);
                } else {
                    file = configXML;
                }

                ConfigXMLLoader.saveConfigFile(config, file.toFile());

            } else {
                throw new IOException(baseDir+" does not exist");
            }
        } catch (JAXBException e) {
            e.printStackTrace();
            throw new IOException(e);

        } catch (IOException e) {
            Logger.getGlobal().severe("Was not able to create file "+  baseDir+ File.separator + configFile);
           throw(e);
        }
    }
}
