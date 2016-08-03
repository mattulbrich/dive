package edu.kit.iti.algover.settings;

import com.sun.scenario.Settings;

import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.util.Properties;

/**
 * ProjectSettings:
 * * symbex settings: unwind loop, inline methods, use contract
 * * ProverSettings: timeout for z3, save intermediate po files
 * * ViewSettings: logical view: display ssa; automatically apply simplification, fontsize, tooltipsize
 * * smt settings for cex
 * TODO group settings into classes and use java properties for saving and loading setting
 * Created by sarah on 8/3/16.
 * has to be called by projectbuilder
 */
public class ProjectSettings {

    public Properties settings;

 /*   public ProjectSettings(File props){
        if(props.exists()) {
            try {
                FileInputStream in = new FileInputStream(props);
                settings = new Properties();
                settings.load(in);
//                for(Settings settings : settingsSet){
//                settings.readSettings(this,properties);
                in.close();

            } catch (FileNotFoundException e) {
                e.printStackTrace();
            } catch (IOException e) {
                e.printStackTrace();
            }

        }
    }*/
}
