package edu.kit.iti.algover.project;

import edu.kit.iti.algover.dafnystructures.DafnyDecl;
import edu.kit.iti.algover.settings.ProjectSettings;
import nonnull.NonNull;

import javax.xml.bind.annotation.*;
import java.io.File;
import java.util.*;

/**
 * Class representing the XML-file that contains all information necessary to create a project
 */
@XmlRootElement
public class Configuration {
    /**
     * The dafny files that are treated as library files, i.e. no proof obligation is generqated for the DafnyDecls in the libarary files
     */
    private List<File> libFiles = new ArrayList<>();
    /**
     * The problem files of a system for which proof obligations should be generated
     */
    private List<File> dafnyFiles = new ArrayList<>();
    /**
     * Settings of the project
     */
    private Map<String, String> projectSettings = new HashMap<>();


    /**
     * If Dafny ProjectManager is used
     */
    @XmlTransient
    private File masterFile = new File("");

    /**
     * If XML Projectmanager is used
     */
    @XmlTransient
    private String configFile = "config.xml";

    private File baseDir = new File("");

    @XmlTransient
    private boolean saveAsXML = false;

    @XmlElement(name = "settings")
    public Map<String, String> getSettings() {
        return projectSettings;
    }

    public void setSettings(Map<String, String> projectSettings) {
        this.projectSettings = projectSettings;
    }

    @XmlElement(name = "libFile")
    public List<File> getLibFiles() {
        return libFiles;
    }

    public void setLibFiles(List<File> libFiles) {
        this.libFiles = libFiles;
    }

    @XmlElement(name = "dafnyFile")
    public List<File> getDafnyFiles() {
        return dafnyFiles;
    }

    public void setDafnyFiles(List<File> dafnyFiles) {
        this.dafnyFiles = dafnyFiles;
    }

    @XmlTransient
    public File getMasterFile() {
        return masterFile;
    }

    public void setMasterFile(File masterFile) {
        this.masterFile = masterFile;
    }

    @XmlTransient
    public String getConfigFile() {
        return configFile;
    }

    public void setConfigFile(String configFile) {
        this.configFile = configFile;
    }

    @XmlElement(name = "baseDir")
    public File getBaseDir() {
        return baseDir;
    }

    public void setBaseDir(File baseDir) {
        this.baseDir = baseDir;
    }

    @XmlTransient
    public boolean isSaveAsXML() {
        return saveAsXML;
    }

    public void setSaveAsXML(boolean saveAsXML) {
        this.saveAsXML = saveAsXML;
    }

}
