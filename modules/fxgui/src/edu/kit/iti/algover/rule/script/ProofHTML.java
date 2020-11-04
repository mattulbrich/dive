package edu.kit.iti.algover.rule.script;

import edu.kit.iti.algover.nuscript.ScriptAST;

import edu.kit.iti.algover.util.Util;
import j2html.tags.Tag;

import java.io.IOException;
import java.util.ArrayList;
import java.util.List;

import static j2html.TagCreator.*;

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

    private final static String JS = readJS();

    /*
     * read the styles from a resource.
     */
    private static String readHead() {
        try {
            return Util.streamToString(ProofHTML.class.getResourceAsStream("ASTStyles.css"));
        } catch (IOException e) {
            e.printStackTrace();
            return "MISSING HEADER";
        }
    }

    private static String readJS() {
        try {
            return Util.streamToString(ProofHTML.class.getResourceAsStream("BlocklyScript.js"));
        } catch (IOException e) {
            e.printStackTrace();
            return "MISSING JS";
        }
    }


    public static String toHTML(ScriptAST.Script script) {
        return html(head(style(HEAD), script().with(rawHtml(JS))), body(toDiv(script))).render();
    }

    /*
     * an entire script as HTML
     */
    private static Tag<?> toDiv(ScriptAST.Script proofScript) {
        return div(attrs("#proofScript.script"), each(proofScript.getStatements(), ProofHTML::toTag));
    }

    /*
     * statements can be commands or cases. Make case distinction here.
     */
    private static Tag<?> toTag(ScriptAST statement) {
        if(statement instanceof ScriptAST.Command) {
            return commandToTag((ScriptAST.Command) statement);
        } else {
            return casesToTag((ScriptAST.Cases) statement);
        }
    }

    private static Tag<?> casesToTag(ScriptAST.Cases cases) {
        return div(attrs(".cases"), span(attrs(".casesName"), "cases"),
                each(cases.getCases(), c ->
                        div(attrs(".case"), span(attrs(".caseLabel"),
                                "case " + (c).getLabel().getText() + ":"),
                                div(attrs(".block"),
                                        each(c.getStatements(), ProofHTML::toTag)))));
    }

    private static Tag<?> commandToTag(ScriptAST.Command command) {
        List<Tag<?>> params = new ArrayList<>();
        params.add(span(attrs(".ruleName"), command.getCommand().getText()));

        for(ScriptAST.Parameter key : command.getParameters()) {
            params.add(span(span(attrs(".paramName"), " " + key.getName().getText() + "="),
                    span(attrs(".termParam"), key.getValue().getText())));
        }

        return div(attrs("#" + command.hashCode() + ".call")).with(params)/*.attr("onclick", "invoke(" + command.hashCode() +");")*/;
    }

}
