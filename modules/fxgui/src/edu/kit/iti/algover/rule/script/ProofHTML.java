package edu.kit.iti.algover.rule.script;

import edu.kit.iti.algover.script.ast.CallStatement;
import edu.kit.iti.algover.script.ast.CasesStatement;
import edu.kit.iti.algover.script.ast.ProofScript;
import edu.kit.iti.algover.script.ast.SimpleCaseStatement;
import edu.kit.iti.algover.script.ast.Statement;
import edu.kit.iti.algover.script.ast.Variable;
import edu.kit.iti.algover.util.Util;
import j2html.tags.Tag;

import java.io.IOException;
import java.util.ArrayList;
import java.util.List;

import static j2html.TagCreator.attrs;
import static j2html.TagCreator.body;
import static j2html.TagCreator.div;
import static j2html.TagCreator.each;
import static j2html.TagCreator.head;
import static j2html.TagCreator.html;
import static j2html.TagCreator.span;
import static j2html.TagCreator.style;

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

    public static String toHTML(ProofScript script) {
        return html(head(style(HEAD)), body(toDiv(script))).render();
    }

    /*
     * an entire script as HTML
     */
    private static Tag<?> toDiv(ProofScript proofScript) {
        return div(attrs(".script"), each(proofScript.getBody().subList(0, proofScript.getBody().size()), ProofHTML::toTag));
    }

    /*
     * statements can be commands or cases. Make case distinction here.
     */
    private static Tag<?> toTag(Statement statement) {
        if(statement instanceof CallStatement) {
            return commandToTag((CallStatement) statement);
        } else {
            return casesToTag((CasesStatement)statement);
        }
    }

    private static Tag<?> casesToTag(CasesStatement cases) {
        return div(attrs(".cases"), span(attrs(".casesName"), "cases"),
                each(cases.getCases(), c ->
                        div(attrs(".case"), span(attrs(".caseLabel"),
                                "case " + ((SimpleCaseStatement)c).getGuard().getText() + ":"),
                                div(attrs(".block"),
                                        each(c.getBody().subList(0, c.getBody().size()), ProofHTML::toTag)))));
    }

    private static Tag<?> commandToTag(CallStatement command) {
        List<Tag<?>> params = new ArrayList<>();
        params.add(span(attrs(".ruleName"), command.getCommand()));
        for(Variable key : command.getParameters().keySet()) {
            params.add(span(span(attrs(".paramName"), " " + key.getIdentifier() + "="),
                    span(attrs(".termParam"), command.getParameters().get(key).getText())));
        }

        return div(attrs(".call")).with(params);
    }

}
