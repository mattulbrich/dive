package edu.kit.iti.algover.smttrans.translate;

import java.util.LinkedHashSet;

import edu.kit.iti.algover.smttrans.data.AxiomContainer;
import edu.kit.iti.algover.term.FunctionSymbol;
import edu.kit.iti.algover.term.Sort;

public class CastDependency extends Dependency {

    public CastDependency(FunctionSymbol fs) {
        super(fs);
        // TODO Auto-generated constructor stub
    }

    @Override
    public LinkedHashSet<String> instantiate() {
        LinkedHashSet<String> inst = new LinkedHashSet<>();

        StringBuilder sb = new StringBuilder();

        sb.append("(declare-fun ");
        sb.append(fs.getName());
        sb.append(" (");
        for (Sort s : fs.getArgumentSorts()) {
            sb.append(s.getName() + " ");
        }
        sb.append(")");
        sb.append(TypeContext.normalizeReturnSort(fs));

        sb.append(")");
        inst.add(sb.toString());
        return inst;
    }

    @Override
    public LinkedHashSet<String> declare() {
        // TODO Auto-generated method stub
        return new LinkedHashSet<>();
    }

}
