/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2018 Karlsruhe Institute of Technology
 *
 */

package edu.kit.iti.algover.nuscript.parser;

import edu.kit.iti.algover.nuscript.BailOutErrorStrategy;
import edu.kit.iti.algover.nuscript.ast.ScriptAST;
import edu.kit.iti.algover.nuscript.parser.ScriptParser.ScriptContext;
import org.antlr.v4.runtime.CharStream;
import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.CommonTokenStream;

import java.io.File;
import java.io.IOException;

public class Scripts {

    public static ScriptAST parseScript(File file) throws IOException {
        return parseScript(CharStreams.fromPath(file.toPath()));
    }

    public static ScriptAST parseScript(String string) {
        return parseScript(CharStreams.fromString(string));
    }

    private static ScriptAST parseScript(CharStream input) {

        CommonTokenStream stream = new CommonTokenStream(new ScriptLexer(input));
        ScriptParser parser = new ScriptParser(stream);

        BailOutErrorStrategy errorHandler = new BailOutErrorStrategy();
        parser.setErrorHandler(errorHandler);
        parser.addErrorListener(errorHandler.ERROR_LISTENER);

        ScriptContext ctx = parser.script();
        ScriptAST result = ctx.accept(new ASTVisitor());

        return result;
    }
}
