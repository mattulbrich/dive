package edu.kit.iti.algover.script;

import edu.kit.iti.algover.nuscript.ast.ScriptAST.Cases;
import edu.kit.iti.algover.nuscript.ast.ScriptAST.Command;
import edu.kit.iti.algover.nuscript.ast.ScriptAST.Script;
import edu.kit.iti.algover.nuscript.ast.ScriptAST.Statement;
import edu.kit.iti.algover.util.Util;
import j2html.tags.Tag;

import static j2html.TagCreator.*;

import java.io.IOException;

/*
 * Container for the static method toHTML that translates a script to a htmlized form.
 *
 * TODO Add this with a conducted proof to learn about errors and open goals.
 *
 * @author Mattias Ulbrich
 */
public final class ProofHTML {

    private ProofHTML() {
        throw new Error("not to be instantiated");
    }

    /**
     * The CSS styles as {@code <style> ... </style>} string.
     */
    private final static String HEAD = readHead();

    /*
     * read the styles from a resource.
     */
    private static String readHead() {
        try {
            return Util.streamToString(ProofHTML.class.getResourceAsStream("css.css"));
        } catch (IOException e) {
            e.printStackTrace();
            return "MISSING HEADER";
        }
    }

    public static String toHTML(Script script) {
        return html(head(style(HEAD)), body(toDiv(script))).render();
    }

    /*
     * an entire script as HTML
     */
    private static Tag<?> toDiv(Script proofScript) {
        return div(attrs(".script"), each(proofScript.getStatements(), ProofHTML::toTag));
    }

    /*
     * statements can be commands or cases. Make case distinction here.
     */
    private static Tag<?> toTag(Statement statement) {
        return statement.visit(ProofHTML::commandToTag, ProofHTML::casesToTag);
    }

    private static Tag<?> casesToTag(Cases cases) {
        return div(attrs(".cases"), span(attrs(".casesName"), "cases"),
            each(cases.getCases(), c ->
                    div(attrs(".case"), span(attrs(".caseLabel"),
                            "case " + c.getLabel().getText() + ":"),
                            div(attrs(".block"),
                                    each(c.getStatements(), ProofHTML::toTag)))));
    }

    private static Tag<?> commandToTag(Command command) {
        return div(attrs(".call"),
                span(attrs(".ruleName"), command.getCommand().getText()),
                each(command.getParameters(), p ->
                        span(span(attrs(".paramName"), " " + p.getName().getText() + "="),
                             span(attrs(".termParam"), p.getValue().getText()))));
    }

}
