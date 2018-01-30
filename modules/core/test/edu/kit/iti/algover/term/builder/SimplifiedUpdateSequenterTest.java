package edu.kit.iti.algover.term.builder;

/*
method m(p : int, m : set<object>) returns (r:int)
  requires p > 0
  ensures r > 0
  modifies m
{
  var local : int;
  local := p;
  if local > 0
  {
     r := local;
  } else {
     r := -local;
  }
}
 */

import edu.kit.iti.algover.data.BuiltinSymbols;
import edu.kit.iti.algover.data.SymbolTable;
import edu.kit.iti.algover.parser.DafnyParserException;
import edu.kit.iti.algover.parser.DafnyTree;
import edu.kit.iti.algover.parser.ParserTest;
import edu.kit.iti.algover.proof.ProofFormula;
import edu.kit.iti.algover.term.Term;
import edu.kit.iti.algover.term.parser.TermParser;
import junitparams.JUnitParamsRunner;
import junitparams.Parameters;
import org.junit.Test;
import org.junit.runner.RunWith;

import java.io.InputStream;

import static org.junit.Assert.assertEquals;

@RunWith(JUnitParamsRunner.class)
public class SimplifiedUpdateSequenterTest extends SequenterTest {

    @Override
    protected PVCSequenter makeSequenter() {
        return new SimplifiedUpdateSequenter();
    }

    @Override
    protected String expectedAntecedent(String pathIdentifier) {
        return "[$gt(p, 0), (let local := p :: $gt(local, 0))]";
    }

    @Override
    protected String expectedSuccedent(String pathIdentifier) {
        return "[(let local := p :: (let r := local :: $gt(r, 0)))]";
    }

    public String[][] parametersForTestIrrelevantLets() {
        return new String[][] {
                { "let x,x2,x3 := 1,2,3 :: let x,y := 2,x :: let z := y :: y==2+x2+z",
                        "let x,x2 := 1,2 :: let y := x :: let z := y :: y==2+x2+z" },
                { "let x := 1 :: let y := 2 :: x>0",
                        "let x := 1 :: x>0"},
                // from a bug:
                { "let x:=1 :: let y:=x :: true", "true"},
        };
    }

    // revealed a problem in the post processing
    @Test @Parameters
    public void testIrrelevantLets(String inputStr, String expectedStr) throws Exception {

        // Only test the postprocessing process. ....

        SymbolTable st = new BuiltinSymbols();
        Term t = TermParser.parse(st, inputStr);
        ProofFormula profForm = new ProofFormula(t);

        SimplifiedUpdateSequenter sus = new SimplifiedUpdateSequenter();
        ProofFormula actual = sus.postProcess(profForm);
        Term expected = TermParser.parse(st, expectedStr);

        assertEquals(expected, actual.getTerm());

    }
}
