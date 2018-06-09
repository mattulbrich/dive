package edu.kit.iti.algover.smttrans.translate.expressions;

import java.util.LinkedHashSet;

import edu.kit.iti.algover.smttrans.data.Operation;
import edu.kit.iti.algover.smttrans.translate.ConstDependency;
import edu.kit.iti.algover.smttrans.translate.Dependency;
import edu.kit.iti.algover.smttrans.translate.Type;
import edu.kit.iti.algover.util.Pair;

public class SMTConstExpression extends SMTExpression {

    private String name;

    public SMTConstExpression(String name, Type type) {
        super(Operation.CONST, type);
        if(name.toLowerCase().equals("null")) {
            this.name = name + type.toString();
        } else {
            this.name = name;
        }
     

    }

    public SMTConstExpression(String name) {
        super(Operation.CONST);
        if(name.toLowerCase().equals("null")) {
            this.name = name + type.toString();
        //} else if (name.startsWith("$")){
          //  this.name = name.replace("$", "");
        //}
        } else {
            this.name = name;
        }
    }

    @Override
    public Pair<LinkedHashSet<Dependency>, String> toSMT() {
        LinkedHashSet<Dependency> set = new LinkedHashSet<>();
        if (!Dependency.isStringNumeric(name)) {
            ConstDependency d = new ConstDependency(name, type);
            set.add(d);
        }

        return new Pair<LinkedHashSet<Dependency>, String>(set,this.name + " ");
    }

}
