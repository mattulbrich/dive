/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
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

    // REVIEW: why is this an extre method?
    public static FileInputStream readFile(File file) throws IOException {
        return new FileInputStream(file);
    }

    /**
     * Searches project directory for file
     * At the moment no error handling if more than one script file exists
     *
     */
    // REVIEW: Is this sensible?
    public static File findFile(File dir, String name) throws FileNotFoundException {
        File f = new File(dir, name);
        if(!f.exists()) {
            throw new FileNotFoundException(f.getAbsolutePath());
        }
        return f;
    }
}
