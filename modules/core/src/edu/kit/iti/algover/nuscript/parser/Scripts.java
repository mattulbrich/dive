/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 *
 */

package edu.kit.iti.algover.nuscript.parser;

import edu.kit.iti.algover.nuscript.BailOutErrorStrategy;
import edu.kit.iti.algover.nuscript.ParentRelationVisitor;
import edu.kit.iti.algover.nuscript.ScriptAST.Script;
import edu.kit.iti.algover.nuscript.parser.ScriptParser.ScriptContext;
import nonnull.NonNull;
import org.antlr.v4.runtime.CharStream;
import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.CommonTokenStream;
import org.antlr.v4.runtime.RecognitionException;

import java.io.File;
import java.io.IOException;
import java.nio.file.Path;

/**
 * Collection of static methods for parsing nuscript scripts from files
 * and strings.
 *
 * @author Mattias Ulbrich
 */
public final class Scripts {

    private Scripts() {
        throw new Error("do not instantiate");
    }

    /**
     * Parse a file into a Script AST data structure.
     * Name resolution and other semantic interpretations are not performed.
     *
     * @param file the file to parse
     * @return the parsing result
     * @throws IOException if the file cannot be read
     * @throws RecognitionException if parsing fails (caution! unchecked exception)
     */
    public static @NonNull Script parseScript(@NonNull File file) throws IOException {
        return parseScript(CharStreams.fromPath(file.toPath()));
    }

    /**
     * Parse a file into a Script AST data structure.
     * Name resolution and other semantic interpretations are not performed.
     *
     * @param path the file to parse
     * @return the parsing result
     * @throws IOException if the file cannot be read
     * @throws RecognitionException if parsing fails (caution! unchecked exception)
     */
    public static @NonNull Script parseScript(@NonNull Path path) throws IOException {
        return parseScript(CharStreams.fromPath(path));
    }

    /**
     * Parse a string into a Script AST data structure.
     * Name resolution and other semantic interpretations are not performed.
     *
     * @param string the string to parse
     * @return the parsing result
     * @throws RecognitionException if parsing fails (caution! unchecked exception)
     */
    public static @NonNull Script parseScript(@NonNull String string) throws RecognitionException {
        return parseScript(CharStreams.fromString(string));
    }

    /*
     * Do the actual parsing returning a script AST.
     */
    private static @NonNull Script parseScript(@NonNull CharStream input) throws RecognitionException {

        CommonTokenStream stream = new CommonTokenStream(new ScriptLexer(input));
        ScriptParser parser = new ScriptParser(stream);

        BailOutErrorStrategy errorHandler = new BailOutErrorStrategy();
        parser.setErrorHandler(errorHandler);
        parser.addErrorListener(errorHandler.ERROR_LISTENER);

        ScriptContext ctx = parser.script();
        Script result = (Script) ctx.accept(new ASTVisitor());

        ParentRelationVisitor.setParentRelation(result);

        return result;
    }
}
