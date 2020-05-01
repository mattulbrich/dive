package edu.kit.iti.algover.script;

import edu.kit.iti.algover.nuscript.ast.ScriptAST.Script;
import edu.kit.iti.algover.nuscript.parser.Scripts;
import org.junit.Test;

public class ProofHTMLTest {

    @Test
    public void testScriptToHTML() throws Exception {

        Script script =
                Scripts.parseScript("command on='term' str=\"string\" b=true;" +
                "cases { case \"c1\": skip; case \"c2\": z3; }");

        String html = ProofHTML.toHTML(script);

        System.out.println(html);
    }

}