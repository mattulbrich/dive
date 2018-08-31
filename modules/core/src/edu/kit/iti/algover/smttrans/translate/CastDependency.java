package edu.kit.iti.algover.smttrans.translate;

import java.util.LinkedHashSet;


import edu.kit.iti.algover.term.FunctionSymbol;
import edu.kit.iti.algover.term.Sort;

public class CastDependency extends Dependency {

    public CastDependency(FunctionSymbol fs, String sort) {
        super(fs);
        if (sort.startsWith("Set")) {
            this.sort = sort.replaceFirst("Set<", "").substring(0, sort.length() - 5);
        } else {
            this.sort = sort;
        }

    }

    private String sort = "";

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

        sb = new StringBuilder();
        inst.add("(declare-fun setin<Object> (Object Set<Object>) Bool)");
        sb.append("(assert (forall\r\n" + "(\r\n" + " (a T)\r\n" + " (s Set<T>)\r\n" + ")\r\n"
                + "(= (setin<Object> (T2o a) (Set<T>2Set<Object> s)) (setin<T> a s))))");

        inst.add(sb.toString().replace("T", sort));
        
        return inst;
    }

    @Override
    public LinkedHashSet<String> declare() {

        return new LinkedHashSet<>();
    }

}
