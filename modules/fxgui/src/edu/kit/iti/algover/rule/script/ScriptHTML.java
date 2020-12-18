package edu.kit.iti.algover.rule.script;

import edu.kit.iti.algover.nuscript.ScriptAST;
import edu.kit.iti.algover.nuscript.ScriptAST.Statement;
import edu.kit.iti.algover.nuscript.ScriptAST.Command;

import edu.kit.iti.algover.util.Util;
import j2html.tags.ContainerTag;
import j2html.tags.Tag;
import org.antlr.v4.runtime.CommonToken;
import org.antlr.v4.runtime.Token;

import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import static j2html.TagCreator.*;

/*
 * Container to translate a ScriptAST.Script to a htmlized form.
 *
 * Also holds mapping for ScriptAST.Statements of proof script to HTML element ID.
 * TODO Add this with a conducted proof to learn about errors and open goals.
 *
 * @author Mattias Ulbrich
 * changed by Valentin Springsklee
 */
public final class ScriptHTML {

    /**
     * The CSS styles as {@code <style> ... </style>} string.
     */
    private final static String HEAD = readHead();

    private final static String JS = readJS();

    private final static String TK_END = "AST_CONT";

    private final Map<ScriptAST, Integer> astElemIDs;

    private Integer count;

    private final ScriptAST.Script proofScript;

    private final String htmlRep;

    public ScriptHTML(ScriptAST.Script proofScript) {
        this.proofScript = proofScript;
        this.count = 0;
        this.astElemIDs = new HashMap<>();
        this.htmlRep = this.createHTML(proofScript);
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


    private String createHTML(ScriptAST.Script script) {
        String htmlScript = html(head(style(HEAD), script().with(rawHtml(JS))), body(toDiv(script))).render();
        astElemIDs.forEach((scriptAST, integer) -> {
            try {
                scriptAST.print(System.out, 0);
            } catch (IOException e) {
                e.printStackTrace();
            }
            System.out.println(integer);

        });
        return htmlScript;
    }

    /*
     * an entire script as HTML
     */
    private Tag<?> toDiv(ScriptAST.Script script) {
        ContainerTag scriptHTMLTag = div(attrs("#proofScript.script"),
                each(script.getStatements(), this::toTag));
        astElemIDs.put(script, count++);
        scriptHTMLTag.with(div(attrs("#" + getID(script) + ".afterLeaf")));
        return scriptHTMLTag;
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
        ContainerTag scriptHTMLTag = div(attrs("#" + c + ".case"), span(attrs(".caseLabel"),
                "case " + (c).getLabel().getText() + ":"),
                div(attrs(".block"),
                        each(c.getStatements(), this::toTag)));
        astElemIDs.put(c, count++);
        scriptHTMLTag.with(div(attrs("#" + getID(c) + ".afterLeaf")));
        return scriptHTMLTag;
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
