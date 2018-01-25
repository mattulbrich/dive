package edu.kit.iti.algover.term.builder;

public class SSASequenterTest extends SequenterTest {

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
    @Override
    protected PVCSequenter makeSequenter() {
        return new SSASequenter();
    }

    @Override
    protected String expectedAntecedent(String pathIdentifier) {
        return "[$eq<set<object>>($mod_1, m), $eq<int>(local_1, p), $eq<int>(r_1, local_1), $gt(p, 0), $gt(local_1, 0)]";
    }

    @Override
    protected String expectedSuccedent(String pathIdentifier) {
        return "[$gt(r_1, 0)]";
    }
}
