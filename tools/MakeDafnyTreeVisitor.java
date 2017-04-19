/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2016 Karlsruhe Institute of Technology
 */
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.stream.Stream;

public class MakeDafnyTreeVisitor {

    public static void main(String[] args) throws IOException {

        try {
        String directory = args[0];
        String tokenFile = args[1];
        String packageName = args[2];
        String prefix = args[3];

        Stream<String> tokens = parseTokens(Paths.get(tokenFile));

        PrintWriter visitor = newPrintWriter(Paths.get(directory, prefix + "TreeVisitor.java"));
        visitor.printf("package %s;%n%npublic interface %sTreeVisitor<R,A> {%n", packageName, prefix);

        PrintWriter defVis = newPrintWriter(Paths.get(directory, prefix + "TreeDefaultVisitor.java"));
        defVis.printf("package %s;%n%npublic class %sTreeDefaultVisitor<R,A> implements %sTreeVisitor<R,A> {%n",
                packageName, prefix, prefix);

        PrintWriter dispatch = newPrintWriter(Paths.get(directory, prefix + "Dispatch.java"));
        dispatch.printf("package %s;%n%nclass %sDispatch {%n"
                + " static <R, A> R dispatch(%sTreeVisitor<R,A> v, %sTree t, A a) {%n"
                + "  switch(t.getType()) {%n", packageName, prefix, prefix, prefix);

        tokens.forEach(t -> {
            visitor.printf("  public R visit%s(%sTree tree, A arg);%n",
                    t, prefix);
            defVis.printf("  @Override public R visit%s(%sTree t, A a) { "
                    + "return visitDefault(t, a); }%n", t, prefix);
            dispatch.printf("  case %sParser.%s:%n    return v.visit%s(t, a);%n",
                    prefix, t, t);
        });

        // NIL
        visitor.printf("  public R visitNIL(%sTree tree, A arg);%n", prefix);
        defVis.printf("  @Override%n  public R visitNIL(%sTree t, A a) { "
                    + "return visitDefault(t, a); }%n", prefix);
        dispatch.printf("  case 0: /* which is the NIL case*/%n    return v.visitNIL(t, a);%n", prefix);

        visitor.println("}");
        visitor.close();

        defVis.printf("  public R visitDefault(%sTree t, A arg) { return null; }\n}", prefix);
        defVis.close();

        dispatch.println("  default: throw new Error(\"uncovered case: \" + t.getType());\n  }\n }\n}");
        dispatch.close();
        } catch(Throwable e) {
            e.printStackTrace();
            System.exit(-1);
        }
    }

    private static PrintWriter newPrintWriter(Path path) throws IOException {
        return new PrintWriter(new FileWriter(path.toString()));
    }

    private static Stream<String> parseTokens(Path path) throws IOException {
        try {
            return Files.lines(path)
                    .filter(l -> !l.startsWith("'") && !l.contains("__"))
                    .map(l -> l.substring(0, l.indexOf('=')));
        } catch (Exception e) {
            throw new IOException("Error while reading " + path.toAbsolutePath(), e);
        }
    }

}
