package edu.kit.iti.algover.project;

import edu.kit.iti.algover.dafnystructures.DafnyDecl;
import edu.kit.iti.algover.settings.ProjectSettings;

import javax.xml.bind.annotation.XmlElement;
import javax.xml.bind.annotation.XmlRootElement;
import java.io.File;
import java.util.List;
import java.util.Map;

/**
 * Class representing the XML-file that contains all information necessary to create a project
 */
@XmlRootElement
public class Configuration {
    public DafnyDecl dafnyDeclarations;
    /**
     * The dafny files that are treated as library files, i.e. no proof obligation is generqated for the DafnyDecls in the libarary files
     */
    private List<File> libFiles;
    /**
     * The problem files of a system for which proof obligations should be generated
     */
    private List<File> dafnyFiles;
    /**
     * Settings of the project
     */
    private Map<String, String> projectSettings;

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


}
