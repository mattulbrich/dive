package edu.kit.iti.algover.smttrans.translate;

import java.util.ArrayList;

import java.util.Arrays;
import java.util.List;

import com.google.common.base.CharMatcher;
import com.google.common.base.Splitter;
import com.google.common.collect.Iterables;

import edu.kit.iti.algover.smttrans.data.OperationMatcher;

import edu.kit.iti.algover.smttrans.data.OperationType;

public class Type {

    private final String ARRNAME = "array";

    private List<String> typeData;

    public Type(List<String> types) {
        this.typeData = inferType(types);

    }

    public static Type typeOperation(String poly) {

        String typedOp = CharMatcher.anyOf(">").removeFrom(poly);
        Iterable<String> operators = Splitter.on("<").split(typedOp);
        List<String> ops = Arrays.asList(Iterables.toArray(operators, String.class));
        return new Type(ops);

    }

    private List<String> inferType(List<String> data) {
        List<String> type = new ArrayList<>();
        for (String d : data) {
            if (d.startsWith("$")) { // function
                OperationType opt = OperationMatcher.matchOp(d).getType();
                if (opt == OperationType.ANY)
                    continue;
                d = opt.getSMT();
            }
            System.out.println("NAME " + d);
            if (d.toLowerCase().equals(ARRNAME))
                d = OperationType.ARR.getSMT();
            type.add(d);
        }
        return type;
    }

    @Override
    public String toString() {
        String ty = "";
        for (String s : this.typeData) {
            ty += s.substring(0, 1).toUpperCase() + s.substring(1);
        }
        return ty;
    }
}
