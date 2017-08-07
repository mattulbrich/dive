package edu.kit.iti.algover.script.parser;

/*-
 * #%L
 * ProofScriptParser
 * %%
 * Copyright (C) 2017 Application-oriented Formal Verification
 * %%
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as
 * published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 * 
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 * 
 * You should have received a copy of the GNU General Public
 * License along with this program.  If not, see
 * <http://www.gnu.org/licenses/gpl-3.0.html>.
 * #L%
 */

import edu.kit.iti.algover.script.ScriptLanguageLexer;
import edu.kit.iti.algover.script.ScriptLanguageParser;
import edu.kit.iti.algover.script.ast.ASTNode;
import edu.kit.iti.algover.script.ast.ProofScript;
import org.antlr.v4.runtime.CharStream;
import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.CommonTokenStream;
import org.antlr.v4.runtime.ParserRuleContext;

import java.io.File;
import java.io.IOException;
import java.util.List;

/**
 * This class captures high-level functions of this package.
 *
 * @author Alexander Weigl
 * @version 1 (27.04.17)
 */
public abstract class Facade {
    /**
     * Parses the given {@link CharStream} and returns the {@link ParserRuleContext}.
     *
     * @param stream containing the proof script
     * @return
     */
    public static ScriptLanguageParser getParser(CharStream stream) {
        ScriptLanguageParser slp = new ScriptLanguageParser(new CommonTokenStream(new ScriptLanguageLexer(stream)));
        return slp;
    }


    /**
     * Parses the given {@link CharStream} and returns the {@link ParserRuleContext}.
     *
     * @param stream containing the proof script
     * @return
     */
    public static ScriptLanguageParser.StartContext parseStream(CharStream stream) {
        return getParser(stream).start();
    }

    /**
     * Parses the given proof script from <code>stream</code> into an AST.
     *
     * @param stream
     * @return
     */
    public static List<ProofScript> getAST(CharStream stream) {
        TransformAst astt = new TransformAst();
        ScriptLanguageParser.StartContext ctx = parseStream(stream);
        if (ctx.exception != null) throw ctx.exception;
        ctx.accept(astt);
        return astt.getScripts();
    }

    /**
     * Parses an AST from the given <code>inputfile</code>
     *
     * @param inputfile
     * @return
     * @throws IOException
     */
    public static List<ProofScript> getAST(File inputfile) throws IOException {
        return getAST(CharStreams.fromPath(inputfile.toPath()));
    }

    public static List<ProofScript> getAST(String input) {
        return getAST(CharStreams.fromString(input));
    }

    /**
     * Returns a prettified output of the given AST.
     *
     * @param node
     * @return
     */
    public static String prettyPrint(ASTNode node) {
        PrettyPrinter prettyPrinter = new PrettyPrinter();
        node.accept(prettyPrinter);
        return prettyPrinter.toString();
    }
}
