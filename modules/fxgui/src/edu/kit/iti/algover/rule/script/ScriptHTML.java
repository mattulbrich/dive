package edu.kit.iti.algover.rule.script;

import edu.kit.iti.algover.nuscript.ScriptAST;

import edu.kit.iti.algover.util.Util;
import j2html.tags.Tag;

import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import static j2html.TagCreator.*;

/*
 * Container for the static method toHTML that translates a script to a htmlized form.
 *
 * TODO Add this with a conducted proof to learn about errors and open goals.
 *
 * @author Mattias Ulbrich
 */
public final class ScriptHTML {

    /**
     * The CSS styles as {@code <style> ... </style>} string.
     */
    private final static String HEAD = readHead();

    private final static String JS = readJS();

    private final Map<ScriptAST, Integer> astElemIDs;

    private Integer count;

    private final ScriptAST.Script proofScript;

    private final String htmlRep;

    public ScriptHTML(ScriptAST.Script proofScript) {
        this.proofScript = proofScript;
        this.count = 0;
        this.astElemIDs = new HashMap<>();
        this.htmlRep = this.toHTML(proofScript);
    }

    public String getHTML() {
        return htmlRep;
    }

    public Integer getID(ScriptAST astElem) {
        return astElemIDs.get(astElem);
    }

    /*
     * read the styles from a resource.
     */
    private static String readHead() {
        try {
            return Util.streamToString(ScriptHTML.class.getResourceAsStream("ASTStyles.css"));
        } catch (IOException e) {
            e.printStackTrace();
            return "MISSING HEADER";
        }
    }

    private static String readJS() {
        try {
            return Util.streamToString(ScriptHTML.class.getResourceAsStream("BlocklyScript.js"));
        } catch (IOException e) {
            e.printStackTrace();
            return "MISSING JS";
        }
    }


    private String toHTML(ScriptAST.Script script) {
        String htmlScript = html(head(style(HEAD), script().with(rawHtml(JS))), body(toDiv(script))).render();
        return htmlScript;
    }

    /*
     * an entire script as HTML
     */
    private Tag<?> toDiv(ScriptAST.Script proofScript) {
        return div(attrs("#proofScript.script"), each(proofScript.getStatements(), this::toTag));
    }

    /*
     * statements can be commands or cases. Make case distinction here.
     */
    private Tag<?> toTag(ScriptAST statement) {
        if(statement instanceof ScriptAST.Command) {
            return commandToTag((ScriptAST.Command) statement);
        } else {
            return casesToTag((ScriptAST.Cases) statement);
        }
    }

    private Tag<?> casesToTag(ScriptAST.Cases cases) {
        astElemIDs.put(cases, count++);
        return div(attrs("#" + getID(cases) + ".cases"), span(attrs(".casesName"), "cases"),
                each(cases.getCases(), this::caseToTag));
    }

    private Tag<?> caseToTag(ScriptAST.Case c) {
        astElemIDs.put(c, count++);
        return div(attrs("#" + c.toString() + ".case"), span(attrs(".caseLabel"),
                "case " + (c).getLabel().getText() + ":"),
                div(attrs(".block"),
                        each(c.getStatements(), this::toTag)));
    }

    private Tag<?> commandToTag(ScriptAST.Command command) {
        List<Tag<?>> params = new ArrayList<>();
        params.add(span(attrs(".ruleName"), command.getCommand().getText()));

        for(ScriptAST.Parameter key : command.getParameters()) {
            params.add(span(span(attrs(".paramName"), " " + key.getName().getText() + "="),
                    span(attrs(".termParam"), key.getValue().getText())));
        }

        this.astElemIDs.put(command, this.count++);

        return div(attrs("#" + getID(command).toString() + ".call")).with(params);
    }

}
