package edu.kit.iti.algover.script;

import edu.kit.iti.algover.nuscript.ast.ScriptAST.Cases;
import edu.kit.iti.algover.nuscript.ast.ScriptAST.Command;
import edu.kit.iti.algover.nuscript.ast.ScriptAST.Script;
import edu.kit.iti.algover.nuscript.ast.ScriptAST.Statement;
import edu.kit.iti.algover.util.Util;
import j2html.tags.Tag;

import static j2html.TagCreator.*;

import java.io.IOException;

public class ProofHTML {

    private static String HEAD = readHead();

    private static String readHead() {
        try {
            return Util.streamToString(ProofHTML.class.getResourceAsStream("css.css"));
        } catch (IOException e) {
            e.printStackTrace();
            return "MISSING HEADER";
        }
    }

    public static String toHTML(Script script) {
        ProofHTML xml = new ProofHTML();
        return html(head(style(HEAD)), body(xml.toDiv(script))).render();
    }

    private Tag toDiv(Script proofScript) {
        return div(attrs(".script"), each(proofScript.getStatements(), this::toTag));
    }

    private Tag toTag(Statement statement) {
        return statement.visit(this::commandToTag, this::casesToTag);
    }

    private Tag casesToTag(Cases cases) {
        return div(attrs(".cases"), span(attrs(".casesName"), "cases"),
            each(cases.getCases(), c ->
                    div(attrs(".case"), span(attrs(".caseLabel"),
                            "case " + c.getLabel().getText() + ":"),
                            div(attrs(".block"),
                                    each(c.getStatements(), this::toTag)))));
    }

    private Tag commandToTag(Command command) {
        return div(attrs(".call"),
                span(attrs(".ruleName"), command.getCommand().getText()),
                each(command.getParameters(), p ->
                        span(span(attrs(".paramName"), " " + p.getName().getText() + "="),
                             span(attrs(".termParam"), p.getValue().getText()))));
    }

}
