/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2017 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.util;

import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.IOException;

/**
 * Created by sarah on 8/16/16.
 */
public class FileUtil {

    public static FileInputStream readFile(File file) throws IOException {
        return new FileInputStream(file);
    }

    /**
     * Searches project directory for file
     * At the moment no error handling if more than one script file exists
     *
     */
    public static File findFile(File dir, String name) throws FileNotFoundException{
        File[] allFilesinDir = dir.listFiles();
        for (File f: allFilesinDir) {
            if(f.getName().equals(name)){
                return f;
            }
        }
        throw new FileNotFoundException("No file exists with name "+name);


    }
}
