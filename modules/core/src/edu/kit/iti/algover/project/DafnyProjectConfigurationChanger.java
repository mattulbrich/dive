/**
 * This file is part of DIVE.
 *
 * Copyright (C) 2015-2019 Karlsruhe Institute of Technology
 */
package edu.kit.iti.algover.project;

import edu.kit.iti.algover.parser.DafnyLexer;
import edu.kit.iti.algover.parser.DafnyParserException;
import edu.kit.iti.algover.util.Util;
import nonnull.NonNull;
import org.antlr.runtime.ANTLRReaderStream;
import org.antlr.runtime.Token;

import java.io.File;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.util.HashSet;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

public class DafnyProjectConfigurationChanger {

    private static final String END_OF_SETTINGS = "// ---- End of settings ----";
    private static final String BEGIN_OF_SETTINGS = "// ---- Automatically generated settings ----";

    private static String ALGOVER_ESCAPE = "//>";


    /**
     * Modify the dafny file named filename in such a fashion that the contained
     * configuration reflects the configuration given by config.
     *
     * It is questionable if it makes sense to set this from outside the editor,
     * but the parallel to the XML file format is there.
     *
     * If the file exists, then it is adapted (modification / extension of the
     * header). It must be a valid, parsable dafny file, this will fail
     * otherwise!
     *
     * If it does not yet exist, it is created.
     *
     * @param config the configuration to save.
     * @param file the name of the file to write.
     * @throws ...
     */

    public static void saveConfiguration(@NonNull Configuration config, @NonNull File file) throws IOException, DafnyParserException {


        if (!file.exists()) {
            try (FileWriter fw = new FileWriter(file)) {
                writeConfig(fw, config);
                return;
            }
        }

        try (FileReader fileReader = new FileReader(file)) {
            ANTLRReaderStream input = new ANTLRReaderStream(fileReader);


            DafnyLexer lexer = new DafnyLexer(input);

            Token token = lexer.nextToken();

            try (FileWriter fw = new FileWriter(file)) {
                loop:
                while (token.getType() != DafnyLexer.EOF) {

                    switch (token.getType()) {
                    case DafnyLexer.METHOD:
                    case DafnyLexer.CLASS:
                    case DafnyLexer.FUNCTION:
                        break loop;

                    case DafnyLexer.MULTILINE_COMMENT:
                    case DafnyLexer.SINGLELINE_COMMENT:
                        String text = token.getText();
                        if(!text.equals(BEGIN_OF_SETTINGS) && !text.equals(END_OF_SETTINGS)) {
                            fw.write(text + "\n");
                        }
                    }

                    token = lexer.nextToken();
                }

                writeConfig(fw, config);

                while (token.getType() != DafnyLexer.EOF) {
                    fw.write(token.getText());
                    token = lexer.nextToken();
                }
            }
        }

    }

    private static void writeConfig(@NonNull FileWriter fw, @NonNull Configuration config) throws IOException {
        fw.write(BEGIN_OF_SETTINGS + "\n");

        fw.write(ALGOVER_ESCAPE + " settings {\n");

        boolean first = true;
        Map<String, String> settings = config.getSettings();
        for (Entry<String, String> entry : settings.entrySet()) {
            if (first) {
                first = false;
            } else {
                fw.write(",\n");
            }
            fw.write(ALGOVER_ESCAPE + "    \"" + entry.getKey() + "\" = \"" + entry.getValue() + "\"");
        }
        fw.write("\n" + ALGOVER_ESCAPE + " }\n");
        for (File libFile : config.getLibFiles()) {
            String fileString = libFile.getPath();
            fw.write(Util.duplicate(" ", ALGOVER_ESCAPE.length()) + " include \"" + fileString + "\"\n");
        }

        first = true;
        for (File dafnyFile : config.getDafnyFiles()) {
            if (first) {
                // The first file is always the input file itself.
                first = false;
            } else {
                String fileString = dafnyFile.getPath();
                fw.write(ALGOVER_ESCAPE + " subsume \"" + fileString + "\"\n");
            }
        }

        fw.write(END_OF_SETTINGS + "\n\n");
    }
}