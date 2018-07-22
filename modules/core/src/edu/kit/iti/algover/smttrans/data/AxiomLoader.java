package edu.kit.iti.algover.smttrans.data;

import java.io.File;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.List;
import java.util.stream.Collectors;
import java.util.stream.Stream;

public class AxiomLoader {
    private static final String dir = "modules/core/res/edu/kit/iti/algover/smttrans/axioms".replace('/',
            File.separatorChar);

    private static List<String> axioms = new ArrayList<>();

    public static void load() {
        Stream<String> stream = null;
        try {
            List<Path> paths = Files.walk(Paths.get(dir)).filter(Files::isRegularFile).collect(Collectors.toList());
            for (Path p : paths) {
                stream = Files.lines(p);
                axioms = matchAxioms(stream.filter(x -> !x.startsWith(";")).filter(x -> !x.trim().isEmpty()).collect(Collectors.toList()));
            }
        } catch (IOException e) {

        } finally {
            stream.close();

        }

    }

    private static String mergeAxiom(List<String> a) {
        String ax = "";
        for (String s : a) {
            ax += s;
        }

        return ax;

    }

    private static List<String> matchAxioms(List<String> lines) {
        List<String> axioms = new ArrayList<>();
        List<String> current = new ArrayList<>();
        int b = 0;
        for (String l : lines) {
            current.add(l);
            for (int i = 0; i < l.length(); i++) {
                if (l.charAt(i) == '(')
                    b++;
                if (l.charAt(i) == ')')
                    b--;
            }

            if (b == 0) {
                axioms.add(mergeAxiom(current));
                current.clear();
            }

        }
        System.out.println(axioms.toString());
        return axioms;

    }

}
