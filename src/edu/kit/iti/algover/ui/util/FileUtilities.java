package edu.kit.iti.algover.ui.util;

import edu.kit.iti.algover.Main;
import edu.kit.iti.algover.ui.model.ProblemLoader;
import javafx.stage.FileChooser;
import javafx.stage.Stage;
import javafx.util.Pair;

import java.io.*;

/**
 * Created by sarah on 9/8/15.
 */
public class FileUtilities {

    public static Pair<File, String> fileOpenAction(Stage stage){


        FileChooser fileChooser = new FileChooser();
        File file = fileChooser.showOpenDialog(stage);
        //ProblemLoader.readFile(file);
        readFile(file);
        String text= "";
        String textline="";
        int line= 1;
        BufferedReader br = readFile(file);

        if(br != null) {

            while (textline != null) {
                try {
                        textline = br.readLine();
                        if(textline==null) break;
                        text += textline + "\n";
                    //text += line + ": " + textline + "\n";
                    //line++;
                } catch (IOException e) {
                    e.printStackTrace();
                }

            }
            try {
                br.close();
            } catch (IOException e) {
                e.printStackTrace();
            }
            return new Pair<File,String>(file, text);




        }else {
            return new Pair<File, String>( file, "File not read");

        }

    }

    public static BufferedReader readFile(File file) {
        try {
            BufferedReader br = new BufferedReader(new FileReader(file));
            return br;


        } catch (FileNotFoundException e) {
            System.out.println("Could not read file " + file.getAbsolutePath());
        } catch (Exception e) {
            System.out.println("Could not load problem");
        }return null;


    }

    public static void fileSaveAction(Stage window, String text){
        FileChooser fc = new FileChooser();
        File file = fc.showSaveDialog(window);
        saveTextToFile(text, file);
    }

    public static Boolean saveTextToFile(String Text, File file){
        Boolean success;
        try {
            FileWriter fw = new FileWriter(file);
            fw.write(Text);
            fw.close();
            success = true;
            return success;
        } catch (IOException e) {
            //e.printStackTrace();
            success = false;
            System.out.println("Error writing to  file "+file.getAbsolutePath());
            return success;
        }


    }
}
