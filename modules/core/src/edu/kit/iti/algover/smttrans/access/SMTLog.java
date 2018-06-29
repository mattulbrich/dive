package edu.kit.iti.algover.smttrans.access;

import java.io.IOException;

import java.nio.file.FileSystems;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.Arrays;
import java.util.List;

public class SMTLog {


public static void writeFile(String smt, String name) {
    
    List<String> lines = Arrays.asList(smt.split("\r\n")); //((?<=\\R)|(?=\\R))
    String seperator = FileSystems.getDefault().getSeparator();
    Path file = Paths.get("." + seperator + name.replace("/", ""));
    
    
    try {
        Files.deleteIfExists(file);
        Files.write(file, lines);
    } catch (IOException e) {
               e.printStackTrace();
    }
    
}

}

