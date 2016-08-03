import java.io.File;
import java.util.LinkedList;

/**
 * Class building a project in AlgoVer
 * Created by sarah on 8/3/16.
 */
public class ProjectBuilder {
    /**List of all files in the project directory
     *
     *
     */
    private File[] allFilesinDir;

    public File[] getAllFilesinDir() {
        return allFilesinDir;
    }

    public void setAllFilesinDir(File[] allFilesinDir) {
        this.allFilesinDir = allFilesinDir;
    }

    public Project getProject() {
        return project;
    }

    public void setProject(Project project) {
        this.project = project;
    }

    /**
     * The object representing a project
     */
    private Project project;

    public ProjectBuilder(File projectPath){
        this.setAllFilesinDir(projectPath.listFiles());
        this.setProject(buildProject(projectPath));
    }

    private Project buildProject(File projectPath){
        File script = findScriptFile();
        LinkedList<File> problemFiles = findProblemFiles();
        return new Project(projectPath, script, problemFiles);

    }


    private LinkedList<File> findProblemFiles() {
        LinkedList<File> problemFiles = new LinkedList<File>();
        for (File f : this.getAllFilesinDir()) {
            if(f.getName().endsWith(".dfy")) {
                System.out.println(f.getName());
                problemFiles.add(f);
            }
        }return problemFiles;
    }

    /**
     * Searches project directory for file ending with .script
     * At the moment no error handling if more than one script file exists
     * Creates a new file named project.script if no file exists, its not saved to directory yet
     * @return Scriptfile
     */
    private File findScriptFile(){
        for (File f : this.getAllFilesinDir()) {
            if(f.getName().endsWith(".script")) {
                System.out.println(f.getName());
                return f;
            }
        }
        System.out.println("No script file exists, creating one in the directory and will be called project.script");
        return new File("project.script");

    }
}
