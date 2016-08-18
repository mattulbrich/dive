package edu.kit.iti.algover.project;

import edu.kit.iti.algover.parser.DafnyFileParser;
import edu.kit.iti.algover.parser.DafnyParser;
import edu.kit.iti.algover.parser.DafnyTree;
import edu.kit.iti.algover.script.ScriptParser;
import edu.kit.iti.algover.script.ScriptFileParser;
import edu.kit.iti.algover.script.ScriptTree;
import edu.kit.iti.algover.settings.ProjectSettings;
import edu.kit.iti.algover.util.FileUtil;
import org.antlr.runtime.RecognitionException;
import org.antlr.runtime.tree.CommonTree;
import org.antlr.runtime.tree.Tree;

import java.io.*;
import java.util.LinkedList;
import java.util.List;

/**
 * Class for building a project in AlgoVer
 * Scriptfile should be parsed here to retrieve settings
 * projectsettings need to be retrieved
 * Created by sarah on 8/3/16.
 */
public class ProjectBuilder {

  //  static String testPath = ("/home/sarah/Documents/KIT_Mitarbeiter/DissTool/TestDir/test.dfy");

    /**
     * List of all files in the project directory
     */
    private File[] allFilesinDir;

    /**
     * All imported libraries
     */
    private List<File> libraries;

    /**
     * All Dafnyfiles in the project directory
     */
    private List<File> dafnyFiles;

    /**
     * The project's directory location
     */
    private File dir;



    /**
     * Setting of project
     */
    private ProjectSettings settings;


    public File getScript() {
        return script;
    }

    /**
     * The script of the project
     */
    private File script;

    private List<DafnyFunction> functions;
    private List<DafnyClass> classes;
    private List<DafnyMethod> methods;

    public ProjectSettings getSettings() {
        return settings;
    }

    public List<File> getLibraries() {
        return libraries;
    }

    public List<File> getDafnyFiles() {
        return dafnyFiles;
    }

    public File getDir() {
        return dir;
    }


    public ProjectBuilder setLibraries(List<File> libraries) {
        this.libraries = libraries;
        return this;
    }

    public ProjectBuilder setDafnyFiles(List<File> dafnyFiles) {
        this.dafnyFiles = dafnyFiles;
        return this;
    }

    public ProjectBuilder setDir(File dir) {
        this.dir = dir;
        return this;
    }

    public ProjectBuilder setSettings(ProjectSettings settings) {
        this.settings = settings;
        return this;
    }

    public ProjectBuilder setScript(File script) {
        this.script = script;
        return this;
    }

    /**
     * Responsible for building project
     */
    public ProjectBuilder() {

        this.methods = new LinkedList<>();
        this.functions = new LinkedList<>();
        this.classes = new LinkedList<>();

    }

    /**
     * Parse dafnyfile
     *
     * @param file dafnyfile
     * @return parsed file as DafnyTree
     */
    public DafnyTree parseFile(File file) {
        DafnyTree t = null;
        try {
            FileInputStream inputStream = new FileInputStream(file);
            t = DafnyFileParser.parse(inputStream);
        } catch (FileNotFoundException e) {
            System.out.println("Could not read file " + file.getAbsolutePath());
        } catch (Exception e) {

            System.out.println("Could not load problem");
            e.printStackTrace();
        }
        return t;
    }

    /**
     * Build project. Handle calling parsers and calling DafnyDecl Builder
     *
     * @param dir of project
     * @return Project Object
     */
    public Project buildProject(File dir) throws Exception {
        this.setDir(dir);
        ProjectSettings settings = new ProjectSettings();
        this.setSettings(settings); //default settings
        //find files


        File scriptFile = null;
        try {
            scriptFile = FileUtil.findFile(dir, "project.script");
        } catch (FileNotFoundException e) {
            e.printStackTrace();
        }
        if (scriptFile != null) {
            this.setScript(scriptFile);
        } else {
            throw new Exception("Could not build project");
        }
        //call script parser and get parsed Script
        ScriptTree parsedScript = parseScriptFile(this.getScript());

        //extractSettings from ScriptTree and change settings in data structure
        extractSettings(parsedScript.getFirstChildWithType(ScriptParser.SETTINGS));
        //extract dafnyfiles into datastructure
        extractDafnyFileNames(parsedScript.getFirstChildWithType(ScriptParser.IMPORT));

        //extract Dafbnylib files into datastructure
        extractDafnyFileNames(parsedScript.getFirstChildWithType(ScriptParser.LIBRARY));
        //parse DafnyFiles
        //atm only one dafnyfile possible (the first in the list)
        DafnyTree parsed = parseFile(this.getDafnyFiles().get(0));
        DafnyDeclVisitor visitor = new DafnyDeclVisitor(this, dir.getName());
        visitor.visit(dir.getName(), parsed);

       // System.out.println(this.settings.toString());
        return new Project(this);
    }

    /**
     * Extract DafnyFilenames from a subtree that has import as root and create new File with current Directory
     */
    public void extractDafnyFileNames(ScriptTree t) {
        List<ScriptTree> dafnyF = t.getChildrenWithType(ScriptParser.FILE);
        List<File> dafnyFilesTemp = new LinkedList<>();
        for (ScriptTree tree : dafnyF) {
            File f = new File(this.dir + File.separator + tree.getChild(0).getText() + tree.getChild(1).getText());
            dafnyFilesTemp.add(f);
           // System.out.println(t.getText()+" "+f.getName());

        }
        switch (t.getType()) {
            case ScriptParser.IMPORT:
                this.setDafnyFiles(dafnyFilesTemp);
             //   System.out.println("Set Dafnyfiles");
                break;
            case ScriptParser.LIBRARY:
                this.setLibraries(dafnyFilesTemp);
              //  System.out.println("Set Lib files");
                break;
            default:
              //  System.out.println("Type for files unknown");
        }
    }

    /**
     * Parse Script File and return Tree to traverse
     *
     * @param script
     * @return
     */
    public ScriptTree parseScriptFile(File script) {
        ScriptTree t = null;
        try {

            InputStream scriptStream = FileUtil.readFile(script);
            t = ScriptFileParser.parse(scriptStream);


        } catch (FileNotFoundException e) {
            e.printStackTrace();
        } catch (RecognitionException e) {
            e.printStackTrace();
        } catch (IOException e) {
            e.printStackTrace();
        } catch (Exception e) {
            e.printStackTrace();
        }
        return t;

    }



    public void addFunction(DafnyFunction func) {
        this.functions.add(func);
   /*     if(currentClassBuilder != null)
            currentClassBuilder.addFunction();*/
    }

    public void addClass(DafnyClass dafnyClass) {
        this.classes.add(dafnyClass);
    }

    public void addMethod(DafnyMethod meth) {
        this.methods.add(meth);
    }

    public List<DafnyClass> getClasses() {
        return this.classes;
    }

    public List<DafnyFunction> getFunctions() {
        return this.functions;
    }

    public List<DafnyMethod> getMethods() {
        return this.methods;
    }

    /**
     * Ectract Settings and add them to settingsobject (maybe refactor to settings class)
     * @param t ScriptTree with root node Settings
     */
    public void extractSettings(ScriptTree t){
       List<ScriptTree> sets = t.getChildrenWithType(ScriptParser.SET);
        for (ScriptTree tr: sets) {
            if(tr.getText().equals("dafny_timeout")){
                this.settings.setValue(ProjectSettings.DAFNY_TIMEOUT, tr.getChild(0).toString());
            }
            if(tr.getText().equals("key_timeout")){
                 this.getSettings().setValue(ProjectSettings.KEY_TIMEOUT, tr.getChild(0).toString());
            }

        }
    }

}
