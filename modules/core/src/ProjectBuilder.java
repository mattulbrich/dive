import java.io.File;
import java.io.IOException;
import java.util.LinkedList;

/**
 * Class for building a project in AlgoVer
 * Scriptfile should be parsed here to retrieve settings
 * projectsettings need to be retrieved
 * Created by sarah on 8/3/16.
 */
public final class ProjectBuilder {
    /**List of all files in the project directory
     */
    private static File[] allFilesinDir;

    public static File[] getAllFilesinDir() {
        return allFilesinDir;
    }

    public static void setAllFilesinDir(File[] allFilesinDirP) {
        allFilesinDir = allFilesinDirP;
    }

    private ProjectBuilder() {

    }

    /**
     * Builds a new project structure
     * @param projectPath: Path to project which contains all problem files and one script file
     * @return a project object
     * @throws IOException
     */
    public static Project buildProject(File projectPath) throws IOException{
        if(projectPath.exists()) {
            setAllFilesinDir(projectPath.listFiles());
            File script = findScriptFile();
            LinkedList<File> problemFiles = findProblemFiles();
            return new Project(projectPath, script, problemFiles);

        }else{

            throw new IOException("Directory does not exist :"+projectPath.toString());

        }

    }


    private static LinkedList<File> findProblemFiles() {
        LinkedList<File> problemFiles = new LinkedList<File>();
        for (File f : getAllFilesinDir()) {
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
    private static File findScriptFile(){
        for (File f : getAllFilesinDir()) {
            if(f.getName().endsWith(".script")) {
                System.out.println(f.getName());
                return f;
            }
        }
        System.out.println("No script file exists, creating one in the directory and will be called project.script");
        return new File("project.script");

    }
}
